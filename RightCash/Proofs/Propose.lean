import RightCash.Spec

/-!
# Invariants, and the correctness of one `Propose`

The key invariant is `ChainOK`: the speculation worker's chain *stands for*
exactly the storage state "base view + every currently marked key written
with its entry from the target's write set". Hints, kept blocks, steps and
retargets preserve it; `finish` then turns it into the plain path's state.
-/

set_option linter.unusedSectionVars false

namespace RightCash

variable {K V D : Type} [DecidableEq K]

section Inv
variable (P : Policy K) (H : Hashes K V P.Cons D) (cap : Nat)

/-- Per-node invariant: the policy tracks exactly the write set's keys
(without duplicates), and marks are tracked keys. -/
def NodeOK (n : Node K V D P) : Prop :=
  P.wf (P.cons n.pol) ∧
  (∀ k, (n.ws k).isSome ↔ k ∈ P.tracked (P.cons n.pol)) ∧
  (∀ k ∈ P.marked n.pol, k ∈ P.tracked (P.cons n.pol))

/-- The prediction invariant (design §9.1: "every marked key is represented
either in the latest view or in the queued operations"): the chain is based
on the target's view, and unless it failed, its effective state is the base
with every marked key holding the target's entry. -/
def ChainOK (n : Node K V D P) (c : Chain K V) : Prop :=
  c.base = n.store ∧
  (c.failed = false →
    ∀ k, c.eff k = if k ∈ P.marked n.pol then (n.ws k).bind Entry.toStore else c.base k)

/-- The global invariant of reachable states. -/
structure Inv (sys : Sys K V D P) : Prop where
  node : ∀ i, NodeOK P (sys.nodes i)
  noWorker : sys.worker = false → sys.spec = none
  target_lt : ∀ t c, sys.spec = some (t, c) → t < sys.size
  chain : ∀ t c, sys.spec = some (t, c) → ChainOK P (sys.nodes t) c

end Inv

/-! ## Write-set lemmas -/

theorem finalEntries_isSome (ws : WriteSet K V) (b : List (BatchOp K V)) (k : K) :
    (finalEntries ws b k).isSome ↔ k ∈ b.map BatchOp.key ∨ (ws k).isSome := by
  unfold finalEntries
  rw [Option.isSome_or, Bool.or_eq_true, batchFinal_isSome]

theorem finalEntries_of_not_written (ws : WriteSet K V) (b : List (BatchOp K V)) (k : K)
    (hk : k ∉ b.map BatchOp.key) : finalEntries ws b k = ws k := by
  unfold finalEntries
  rw [(batchFinal_eq_none b k).2 hk, Option.none_or]

theorem mem_evictedOps (ws : WriteSet K V) (b : List (BatchOp K V)) (vs : List K)
    (o : BatchOp K V) :
    o ∈ evictedOps ws b vs ↔
      ∃ k e, k ∈ vs ∧ finalEntries ws b k = some e ∧ o = BatchOp.ofEntry k e := by
  unfold evictedOps
  simp only [List.mem_map, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨ke, ⟨k, hk, e, he, rfl⟩, rfl⟩
    exact ⟨k, e, hk, he, rfl⟩
  · rintro ⟨k, e, hk, he, rfl⟩
    exact ⟨(k, e), ⟨k, hk, e, he, rfl⟩, rfl⟩

section Lawful
variable (P : Policy K) (H : Hashes K V P.Cons D) (cap : Nat) (hP : P.Lawful)
include hP

/-- The plain path writes exactly the victims' final entries. -/
theorem plainStore_eq (par : Node K V D P) (b : List (BatchOp K V)) (vs : List K)
    (hfin : ∀ k ∈ vs, (finalEntries par.ws b k).isSome) :
    plainStore P par b vs =
      fun k => if k ∈ vs then (finalEntries par.ws b k).bind Entry.toStore else par.store k := by
  funext k
  unfold plainStore
  by_cases hV : vs = []
  · subst hV; simp
  · rw [ite_eq_right hV,
      applyBatch_of_vals _ _ (fun k => (finalEntries par.ws b k).bind Entry.toStore)]
    · have hmem : k ∈ (evictedOps par.ws b vs).map BatchOp.key ↔ k ∈ vs := by
        rw [List.mem_map]
        constructor
        · rintro ⟨o, ho, rfl⟩
          obtain ⟨k', e, hk', _, rfl⟩ := (mem_evictedOps _ _ _ _).1 ho
          simpa using hk'
        · intro hk
          obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 (hfin k hk)
          exact ⟨_, (mem_evictedOps _ _ _ _).2 ⟨k, e, hk, he, rfl⟩, by simp⟩
      by_cases hk : k ∈ vs
      · rw [ite_eq_left (hmem.2 hk), ite_eq_left hk]
      · rw [ite_eq_right (mt hmem.1 hk), ite_eq_right hk]
    · intro o ho
      obtain ⟨k', e, _, he, rfl⟩ := (mem_evictedOps _ _ _ _).1 ho
      simp [he]

/-- Actual victims have a final entry (`merge` never hits `unreachable!`). -/
theorem victims_fin (par : Node K V D P) (b : List (BatchOp K V)) (hn : NodeOK P par) :
    ∀ k ∈ (writesOf P cap par b).1.victims, (finalEntries par.ws b k).isSome := by
  intro k hk
  rw [writesOf, hP.writes_victims] at hk
  rw [finalEntries_isSome]
  rcases hP.victims_sub _ _ _ _ k hk with h | h
  · exact Or.inr ((hn.2.1 k).2 h)
  · exact Or.inl h

/-- The reference store of a child, in terms of the implementation's victims. -/
theorem specPropose_store (par : Node K V D P) (b : List (BatchOp K V)) :
    (specPropose P cap par.state b).store =
      fun k => if k ∈ (writesOf P cap par b).1.victims
        then (finalEntries par.ws b k).bind Entry.toStore else par.store k := by
  simp only [specPropose, Node.state, writesOf, hP.writes_victims]
  rfl

/-- A child built with a policy whose consensus part is the reference one and
with the reference store has the reference state. -/
theorem mkChild_state (par : Node K V D P) (p : Nat) (b : List (BatchOp K V))
    (md : Option (List UInt8)) (pol : P.St) (st : Store K V)
    (hpol : P.cons pol = P.cons (writesOf P cap par b).2)
    (hst : st = (specPropose P cap par.state b).store) :
    (mkChild P H cap par p b md pol st).state = specPropose P cap par.state b := by
  rw [hst]
  simp only [mkChild, Node.state, specPropose, hpol, writesOf, hP.writes_cons, hP.writes_victims]

theorem plainChild_state (par : Node K V D P) (p : Nat) (b : List (BatchOp K V))
    (md : Option (List UInt8)) (hn : NodeOK P par) :
    (plainChild P H cap par p b md).state = specPropose P cap par.state b := by
  apply mkChild_state P H cap hP
  · exact hP.reset_cons _
  · rw [specPropose_store P cap hP, plainStore_eq P hP par b _ (victims_fin P cap hP par b hn)]

/-- **Speculative finalization equals the plain path** (design §9.1). If the
chain satisfies the prediction invariant for the parent, then the view that
`finish` returns has exactly the reference storage state. -/
theorem finish_store (par : Node K V D P) (b : List (BatchOp K V)) (md : Option (List UInt8))
    (ok : Bool) (c : Chain K V) (st : Store K V) (hn : NodeOK P par) (hc : ChainOK P par c)
    (hne : (writesOf P cap par b).1.victims ≠ [])
    (h : c.finish (specOps (finalEntries par.ws b) (writesOf P cap par b).1.evict
      (writesOf P cap par b).1.retract) md ok = some st) :
    st = (specPropose P cap par.state b).store := by
  obtain ⟨hfail, hst⟩ := Chain.finish_some _ _ _ _ _ h
  obtain ⟨hbase, heff⟩ := hc
  obtain ⟨hE, hVE, hmR, hRV⟩ :
      FinalOK (P.marked par.pol) (b.map BatchOp.key) (writesOf P cap par b).1 :=
    hP.final _ _ _ _ hne
  have hfin := victims_fin P cap hP par b hn
  rw [specPropose_store P cap hP]
  funext k
  rw [hst, Chain.eff_submit_specOps _ _ _ _ hfail, heff hfail k, hbase]
  -- abbreviations for readability
  generalize hW : writesOf P cap par b = W at *
  by_cases hR : k ∈ W.1.retract
  · rw [ite_eq_left hR, ite_eq_right (hRV k hR)]
  · rw [ite_eq_right hR]
    by_cases hEk : k ∈ W.1.evict
    · rw [ite_eq_left hEk, ite_eq_left (hE k hEk)]
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 (hfin k (hE k hEk))
      rw [he]; rfl
    · rw [ite_eq_right hEk]
      by_cases hV : k ∈ W.1.victims
      · obtain ⟨hm, hnw⟩ := hVE k hV hEk
        rw [ite_eq_left hm, ite_eq_left hV, finalEntries_of_not_written _ _ _ hnw]
      · have hm : k ∉ P.marked par.pol := fun hm => hR (hmR k hm hV)
        rw [ite_eq_right hm, ite_eq_right hV]

/-- **One `Propose`, any path.** Under the invariant, the new node has the
reference state, the given metadata hash and the given parent. -/
theorem proposeOut_child (sys : Sys K V D P) (p : Nat) (b : List (BatchOp K V))
    (md : Option (List UInt8)) (ok : Bool) (hinv : Inv P sys) :
    (proposeOut P H cap sys p b md ok).1.state = specPropose P cap (sys.nodes p).state b ∧
    (proposeOut P H cap sys p b md ok).1.metaHash = H.metadata md ∧
    (proposeOut P H cap sys p b md ok).1.parent = some p := by
  have hn := hinv.node p
  have hplain := plainChild_state P H cap hP (sys.nodes p) p b md hn
  unfold proposeOut
  cases hs : sys.spec with
  | none => exact ⟨hplain, rfl, rfl⟩
  | some tc =>
    obtain ⟨t, c⟩ := tc
    simp only
    by_cases ht : t = p
    · subst ht
      simp only [ite_true]
      by_cases hV : (writesOf P cap (sys.nodes t) b).1.victims = []
      · simp only [hV, ite_true]
        refine ⟨?_, rfl, rfl⟩
        apply mkChild_state P H cap hP _ _ _ _ _ _ rfl
        rw [specPropose_store P cap hP, hV]
        funext k; simp
      · simp only [hV, ite_false]
        unfold finishChild
        cases hf : c.finish (specOps (finalEntries (sys.nodes t).ws b)
            (writesOf P cap (sys.nodes t) b).1.evict
            (writesOf P cap (sys.nodes t) b).1.retract) md ok with
        | none => exact ⟨hplain, rfl, rfl⟩
        | some st =>
          refine ⟨?_, rfl, rfl⟩
          apply mkChild_state P H cap hP _ _ _ _ _ _ rfl
          exact finish_store P cap hP _ b md ok c st hn (hinv.chain t c hs) hV hf
    · simp only [ht, ite_false]
      exact ⟨hplain, rfl, rfl⟩

end Lawful

end RightCash
