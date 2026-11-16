import RightCash.Proofs.Propose

/-!
# Preservation of the invariant

Every transition of the engine preserves `Inv`; the initial state satisfies
it. The interesting cases are the ones that touch the worker's chain:

* `retarget` re-establishes `ChainOK` from scratch (reset + resend marks);
* a hint changes marks and submits ops describing exactly that change
  (`MarkDelta`);
* a non-evicting block on the target keeps the chain, refreshing rewritten
  predictions or withdrawing them;
* a worker step does not change the chain's effective state.
-/

set_option linter.unusedSectionVars false

namespace RightCash

variable {K V D : Type} [DecidableEq K]

section Lawful
variable (P : Policy K) (H : Hashes K V P.Cons D) (cap : Nat) (hP : P.Lawful)
include hP

theorem nodeOK_dom {n : Node K V D P} (hn : NodeOK P n) {k : K}
    (hk : k ∈ P.tracked (P.cons n.pol)) : ∃ e, n.ws k = some e :=
  Option.isSome_iff_exists.1 ((hn.2.1 k).2 hk)

/-! ## Retarget -/

theorem retargetChain_ok (n : Node K V D P) (hn : NodeOK P n) :
    ChainOK P n (retargetChain P n) := by
  refine ⟨by simp [retargetChain, Chain.new], fun hf k => ?_⟩
  have hf' : (Chain.new n.store : Chain K V).failed = false := rfl
  unfold retargetChain
  rw [Chain.eff_submit_specOps _ _ _ _ hf', hP.predicted_eq]
  simp only [List.not_mem_nil, ite_false, Chain.eff_new, Chain.submit_base]
  by_cases hm : k ∈ P.marked n.pol
  · rw [ite_eq_left hm, ite_eq_left hm]
    obtain ⟨e, he⟩ := nodeOK_dom P hP hn (hn.2.2.1 k hm)
    rw [he]; rfl
  · rw [ite_eq_right hm, ite_eq_right hm]; rfl

theorem inv_of_spec (sys : Sys K V D P) (spec' : Option (Nat × Chain K V))
    (hinv : Inv P sys)
    (hw : sys.worker = false → spec' = none)
    (hs : ∀ t c, spec' = some (t, c) → t < sys.size ∧ ChainOK P (sys.nodes t) c) :
    Inv P { sys with spec := spec' } :=
  ⟨hinv.node, hw, fun t c h => (hs t c h).1, fun t c h => (hs t c h).2⟩

theorem inv_retarget (sys : Sys K V D P) (i : Nat) (hinv : Inv P sys) (hi : i < sys.size) :
    Inv P (sys.retarget P i) := by
  apply inv_of_spec P hP sys _ hinv
  · intro hw; simp [retargetSpec, hw]
  · intro t c h
    unfold retargetSpec at h
    split at h
    · cases h
      exact ⟨hi, retargetChain_ok P hP _ (hinv.node _)⟩
    · cases h

/-! ## Propose -/

theorem mkChild_ok (par : Node K V D P) (p : Nat) (b : List (BatchOp K V))
    (md : Option (List UInt8)) (pol : P.St) (st : Store K V) (hn : NodeOK P par)
    (hcons : P.cons pol = P.cons (writesOf P cap par b).2)
    (hmarks : ∀ k ∈ P.marked pol, k ∈ P.tracked (P.cons pol)) :
    NodeOK P (mkChild P H cap par p b md pol st) := by
  have hcons' : P.cons pol =
      (P.specWrites (P.cons par.pol) (b.map BatchOp.key) (par.height + 1) cap).2 := by
    rw [hcons, writesOf, hP.writes_cons]
  refine ⟨?_, ?_, hmarks, ?_⟩
  · show P.wf (P.cons pol)
    rw [hcons']; exact hP.wf_writes _ _ _ _ hn.1
  · intro k
    show (childWS par.ws b (writesOf P cap par b).1.victims k).isSome ↔ k ∈ P.tracked (P.cons pol)
    rw [hcons', hP.tracked_writes _ _ _ _ _ hn.1, ← hP.writes_victims, ← writesOf]
    unfold childWS
    by_cases hV : k ∈ (writesOf P cap par b).1.victims
    · simp [hV]
    · rw [ite_eq_right hV, finalEntries_isSome, hn.2.1 k]
      simp only [hV, not_false_eq_true, and_true]
      exact Or.comm
  · intro h; simp [mkChild, Node.state] at h

theorem writes_marks_ok (par : Node K V D P) (b : List (BatchOp K V)) (hn : NodeOK P par) :
    ∀ k ∈ P.marked (writesOf P cap par b).2,
      k ∈ P.tracked (P.cons (writesOf P cap par b).2) :=
  hP.writes_marked _ _ _ _ hn.1 hn.2.2.1

theorem plainChild_ok (par : Node K V D P) (p : Nat) (b : List (BatchOp K V))
    (md : Option (List UInt8)) (hn : NodeOK P par) :
    NodeOK P (plainChild P H cap par p b md) :=
  mkChild_ok P H cap hP _ _ _ _ _ _ hn (hP.reset_cons _) (by simp [hP.reset_marked])

theorem finishChild_ok (par : Node K V D P) (p : Nat) (b : List (BatchOp K V))
    (md : Option (List UInt8)) (c : Chain K V) (ok : Bool) (hn : NodeOK P par) :
    NodeOK P (finishChild P H cap par p b md c ok) := by
  unfold finishChild
  split
  · exact mkChild_ok P H cap hP _ _ _ _ _ _ hn rfl (writes_marks_ok P cap hP par b hn)
  · exact plainChild_ok P H cap hP par p b md hn

/-- A non-evicting block on the target keeps the chain valid for the child. -/
theorem kept_chain_ok (par : Node K V D P) (p : Nat) (b : List (BatchOp K V))
    (md : Option (List UInt8)) (c : Chain K V) (hn : NodeOK P par) (hc : ChainOK P par c)
    (hV : (writesOf P cap par b).1.victims = []) :
    ChainOK P (mkChild P H cap par p b md (writesOf P cap par b).2 par.store)
      (c.submit (specOps (childWS par.ws b (writesOf P cap par b).1.victims)
        (writesOf P cap par b).1.evict (writesOf P cap par b).1.retract)) := by
  obtain ⟨hbase, heff⟩ := hc
  obtain ⟨hMD, hres⟩ :
      MarkDelta (P.marked par.pol) (P.marked (writesOf P cap par b).2)
        (writesOf P cap par b).1.evict (writesOf P cap par b).1.retract ∧
      ∀ k ∈ b.map BatchOp.key, k ∈ P.marked (writesOf P cap par b).2 →
        k ∈ (writesOf P cap par b).1.evict :=
    hP.kept_delta _ _ _ _ hV
  have hchild := mkChild_ok P H cap hP par p b md _ par.store hn rfl
    (writes_marks_ok P cap hP par b hn)
  refine ⟨by simp [hbase, mkChild], fun hf k => ?_⟩
  have hf' : c.failed = false := by simpa using hf
  dsimp only [mkChild] at hchild
  show _ = if k ∈ P.marked (writesOf P cap par b).2
    then (childWS par.ws b (writesOf P cap par b).1.victims k).bind Entry.toStore
    else (c.submit _).base k
  rw [Chain.eff_submit_specOps _ _ _ _ hf', heff hf' k, Chain.submit_base, hbase]
  obtain ⟨hR1, hE1, hO1⟩ := hMD k
  by_cases hR : k ∈ (writesOf P cap par b).1.retract
  · rw [ite_eq_left hR, ite_eq_right (hR1 hR)]
  · rw [ite_eq_right hR]
    by_cases hE : k ∈ (writesOf P cap par b).1.evict
    · have hm := hE1 hR hE
      rw [ite_eq_left hE, ite_eq_left hm]
      obtain ⟨e, he⟩ := nodeOK_dom P hP hchild (hchild.2.2.1 k hm)
      simp only at he
      rw [he]; rfl
    · rw [ite_eq_right hE]
      by_cases hm : k ∈ P.marked par.pol
      · have hm' := (hO1 hR hE).2 hm
        have hnw : k ∉ b.map BatchOp.key := fun hw => hE (hres k hw hm')
        rw [ite_eq_left hm, ite_eq_left hm']
        unfold childWS
        rw [hV, finalEntries_of_not_written _ _ _ hnw]
        simp
      · have hm' : k ∉ P.marked (writesOf P cap par b).2 := fun h => hm ((hO1 hR hE).1 h)
        rw [ite_eq_right hm, ite_eq_right hm']

theorem inv_propose (sys : Sys K V D P) (p : Nat) (b : List (BatchOp K V))
    (md : Option (List UInt8)) (ok : Bool) (hinv : Inv P sys) :
    Inv P (sys.propose P H cap p b md ok) := by
  have hn := hinv.node p
  -- nodes: the old ones and one new child, which is always well formed
  have hchildOK : NodeOK P (proposeOut P H cap sys p b md ok).1 := by
    unfold proposeOut
    cases hs : sys.spec with
    | none => exact plainChild_ok P H cap hP _ _ _ _ hn
    | some tc =>
      obtain ⟨t, c⟩ := tc
      simp only
      by_cases ht : t = p
      · subst ht
        simp only [ite_true]
        by_cases hV : (writesOf P cap (sys.nodes t) b).1.victims = []
        · simp only [hV, ite_true]
          exact mkChild_ok P H cap hP _ _ _ _ _ _ hn rfl (writes_marks_ok P cap hP _ b hn)
        · simp only [hV, ite_false]
          exact finishChild_ok P H cap hP _ _ _ _ _ _ hn
      · simp only [ht, ite_false]
        exact plainChild_ok P H cap hP _ _ _ _ hn
  have hnodes : ∀ i, NodeOK P ((sys.propose P H cap p b md ok).nodes i) := by
    intro i
    show NodeOK P (fupd sys.nodes sys.size _ i)
    by_cases hi : i = sys.size
    · subst hi; rw [fupd_same]; exact hchildOK
    · rw [fupd_ne _ _ hi]; exact hinv.node i
  -- old targets keep their node: they sit below `size`
  have hold : ∀ t, t < sys.size → (sys.propose P H cap p b md ok).nodes t = sys.nodes t := by
    intro t ht
    show fupd sys.nodes sys.size _ t = _
    exact fupd_ne _ _ (Nat.ne_of_lt ht)
  have hnew : (sys.propose P H cap p b md ok).nodes sys.size = (proposeOut P H cap sys p b md ok).1 := by
    show fupd sys.nodes sys.size _ sys.size = _
    exact fupd_same _ _ _
  refine ⟨hnodes, ?_, ?_, ?_⟩
  · intro hw
    show (proposeOut P H cap sys p b md ok).2 = none
    have hs := hinv.noWorker hw
    unfold proposeOut; rw [hs]
  · intro t c h
    show t < sys.size + 1
    change (proposeOut P H cap sys p b md ok).2 = some (t, c) at h
    unfold proposeOut at h
    cases hs : sys.spec with
    | none => rw [hs] at h; simp at h
    | some tc =>
      obtain ⟨t', c'⟩ := tc
      rw [hs] at h
      simp only at h
      by_cases ht : t' = p
      · subst ht
        simp only [ite_true] at h
        by_cases hV : (writesOf P cap (sys.nodes t') b).1.victims = []
        · simp only [hV, ite_true, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]; exact Nat.lt_succ_self _
        · simp only [hV, ite_false] at h
          unfold retargetSpec at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1]; exact Nat.lt_succ_self _
          · cases h
      · simp only [ht, ite_false] at h
        exact Nat.lt_succ_of_lt (hinv.target_lt t c (hs.trans h))
  · intro t c h
    change (proposeOut P H cap sys p b md ok).2 = some (t, c) at h
    have h' := h
    unfold proposeOut at h'
    cases hs : sys.spec with
    | none => rw [hs] at h'; simp at h'
    | some tc =>
      obtain ⟨t', c'⟩ := tc
      rw [hs] at h'
      simp only at h'
      by_cases ht : t' = p
      · subst ht
        simp only [ite_true] at h'
        by_cases hV : (writesOf P cap (sys.nodes t') b).1.victims = []
        · simp only [hV, ite_true, Option.some.injEq, Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rw [hnew]
          unfold proposeOut
          rw [hs]
          simp only [ite_true, hV]
          rw [← hV]
          exact kept_chain_ok P H cap hP _ _ _ _ _ hn (hinv.chain _ _ hs) hV
        · simp only [hV, ite_false] at h'
          unfold retargetSpec at h'
          split at h'
          · simp only [Option.some.injEq, Prod.mk.injEq] at h'
            obtain ⟨rfl, rfl⟩ := h'
            rw [hnew]
            unfold proposeOut
            rw [hs]
            simp only [ite_true, hV, ite_false]
            exact retargetChain_ok P hP _ (finishChild_ok P H cap hP _ _ _ _ _ _ hn)
          · cases h'
      · simp only [ht, ite_false] at h'
        rw [hold t (hinv.target_lt t c (hs.trans h'))]; exact hinv.chain t c (hs.trans h')

/-! ## Prefetch -/

/-- A hint keeps the chain valid for the target. -/
theorem hint_chain_ok (n : Node K V D P) (ks : List K) (margin : Nat) (c : Chain K V)
    (hn : NodeOK P n) (hc : ChainOK P n c) :
    ChainOK P { n with pol := (P.hintWrites n.pol ks cap margin).2 }
      (c.submit (specOps n.ws (P.hintWrites n.pol ks cap margin).1.evict
        (P.hintWrites n.pol ks cap margin).1.retract)) := by
  obtain ⟨hbase, heff⟩ := hc
  refine ⟨by simp [hbase], fun hf k => ?_⟩
  have hf' : c.failed = false := by simpa using hf
  show _ = if k ∈ P.marked (P.hintWrites n.pol ks cap margin).2
    then (n.ws k).bind Entry.toStore else (c.submit _).base k
  rw [Chain.eff_submit_specOps _ _ _ _ hf', heff hf' k, Chain.submit_base]
  obtain ⟨hR1, hE1, hO1⟩ := hP.hint_delta n.pol ks cap margin k
  by_cases hR : k ∈ (P.hintWrites n.pol ks cap margin).1.retract
  · rw [ite_eq_left hR, ite_eq_right (hR1 hR)]
  · rw [ite_eq_right hR]
    by_cases hE : k ∈ (P.hintWrites n.pol ks cap margin).1.evict
    · have hm := hE1 hR hE
      rw [ite_eq_left hE, ite_eq_left hm]
      have ht := hP.hint_marked n.pol ks cap margin hn.2.2.1 k hm
      obtain ⟨e, he⟩ := nodeOK_dom P hP hn ht
      rw [he]; rfl
    · rw [ite_eq_right hE]
      by_cases hm : k ∈ P.marked n.pol
      · rw [ite_eq_left hm, ite_eq_left ((hO1 hR hE).2 hm)]
      · have hm' : k ∉ P.marked (P.hintWrites n.pol ks cap margin).2 :=
          fun h => hm ((hO1 hR hE).1 h)
        rw [ite_eq_right hm, ite_eq_right hm']

theorem hinted_node_ok (n : Node K V D P) (ks : List K) (margin : Nat) (hn : NodeOK P n) :
    NodeOK P { n with pol := (P.hintWrites n.pol ks cap margin).2 } := by
  have hc := hP.hint_cons n.pol ks cap margin
  refine ⟨?_, ?_, ?_, ?_⟩
  · show P.wf (P.cons (P.hintWrites n.pol ks cap margin).2); rw [hc]; exact hn.1
  · intro k; show _ ↔ k ∈ P.tracked (P.cons (P.hintWrites n.pol ks cap margin).2)
    rw [hc]; exact hn.2.1 k
  · intro k hk
    show k ∈ P.tracked (P.cons (P.hintWrites n.pol ks cap margin).2)
    rw [hc]; exact hP.hint_marked n.pol ks cap margin hn.2.2.1 k hk
  · intro h
    have := hn.2.2.2 h
    simp only [Node.state] at this ⊢
    rw [hc]; exact this

theorem inv_hint (sys : Sys K V D P) (v : Nat) (ks : List K) (margin : Nat) (hinv : Inv P sys) :
    Inv P (sys.hint P cap v ks margin) := by
  unfold Sys.hint
  cases hs : sys.spec with
  | none => exact hinv
  | some tc =>
    obtain ⟨t, c⟩ := tc
    simp only
    by_cases ht : t = v
    · subst ht
      simp only [ite_true]
      have hn := hinv.node t
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i
        by_cases hi : i = t
        · subst hi; simp only [fupd_same]; exact hinted_node_ok P cap hP _ ks margin hn
        · simp only [fupd_ne _ _ hi]; exact hinv.node i
      · intro hw; rw [hinv.noWorker hw] at hs; cases hs
      · intro t' c' h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; exact hinv.target_lt t c hs
      · intro t' c' h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [fupd_same]
        exact hint_chain_ok P cap hP _ ks margin c hn (hinv.chain t c hs)
    · simp only [ht, ite_false]; exact hinv

theorem inv_prefetch (sys : Sys K V D P) (v : Nat) (ks : List K) (margin : Nat)
    (hinv : Inv P sys) (hv : v < sys.size) : Inv P (sys.prefetch P cap v ks margin) := by
  unfold Sys.prefetch
  split
  · apply inv_hint P cap hP
    split
    · exact inv_retarget P hP sys v hinv hv
    · exact hinv
  · exact hinv

/-! ## Commit, worker, drop -/

theorem inv_setHead (sys : Sys K V D P) (n : Nat) (hinv : Inv P sys) :
    Inv P { sys with head := n } :=
  ⟨hinv.node, hinv.noWorker, hinv.target_lt, hinv.chain⟩

theorem inv_commit (sys : Sys K V D P) (n : Nat) (hinv : Inv P sys) (hn : n < sys.size) :
    Inv P (sys.commit P n) := by
  have h1 := inv_setHead P hP sys n hinv
  unfold Sys.commit
  split
  · split
    · split
      · exact h1
      · exact inv_retarget P hP _ n h1 hn
    · exact inv_retarget P hP _ n h1 hn
  · exact h1

theorem inv_workerStep (sys : Sys K V D P) (ok : Bool) (hinv : Inv P sys) :
    Inv P (sys.workerStep P ok) := by
  unfold Sys.workerStep
  cases hs : sys.spec with
  | none => exact hinv
  | some tc =>
    obtain ⟨t, c⟩ := tc
    simp only
    split
    · apply inv_of_spec P hP sys _ hinv
      · intro hw; rw [hinv.noWorker hw] at hs; cases hs
      · intro t' c' h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hinv.target_lt _ c hs, ?_⟩
        obtain ⟨hbase, heff⟩ := hinv.chain _ c hs
        cases ok
        · exact ⟨hbase, fun hf => by simp at hf⟩
        · refine ⟨hbase, fun hf k => ?_⟩
          simp only [ite_true, Chain.build_failed] at hf ⊢
          rw [Chain.eff_build, heff hf k, Chain.build_base]
    · exact hinv

theorem inv_dropTarget (sys : Sys K V D P) (hinv : Inv P sys) :
    Inv P { sys with spec := none } :=
  inv_of_spec P hP sys none hinv (fun _ => rfl) (fun _ _ h => by cases h)

/-! ## Initial state and all steps -/

theorem inv_init (n0 : Node K V D P) (w : Bool) (h0 : InitOK P n0) :
    Inv P (Sys.init P n0 w) := by
  obtain ⟨hwf, hdom, hgen⟩ := h0
  have hc := hP.reset_cons n0.pol
  have hg : NodeOK P { n0 with pol := P.resetHints n0.pol, parent := none } := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show P.wf (P.cons (P.resetHints n0.pol)); rw [hc]; exact hwf
    · intro k; show _ ↔ k ∈ P.tracked (P.cons (P.resetHints n0.pol)); rw [hc]; exact hdom k
    · intro k hk; simp [hP.reset_marked] at hk
    · intro h
      have := hgen h
      simp only [Node.state, EState.mk.injEq, EState.empty] at this ⊢
      rw [hc]; exact this
  refine ⟨fun _ => hg, ?_, ?_, ?_⟩
  · intro hw
    change w = false at hw
    simp [Sys.init, hw]
  · intro t c h
    simp only [Sys.init] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact Nat.zero_lt_one
    · cases h
  · intro t c h
    simp only [Sys.init] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, fun _ k => ?_⟩
      show (Chain.new n0.store).eff k = if k ∈ P.marked (P.resetHints n0.pol)
        then (n0.ws k).bind Entry.toStore else n0.store k
      simp [hP.reset_marked]
    · cases h

theorem inv_step [DecidableEq D] (s s' : Sys K V D P) (l : Label K V) (hinv : Inv P s)
    (h : Step P H cap s l s') : Inv P s' := by
  cases h with
  | propose p b md ok _ => exact inv_propose P H cap hP s p b md ok hinv
  | commit n hn _ _ => exact inv_commit P hP s n hinv hn
  | prefetch v ks margin hv => exact inv_prefetch P cap hP s v ks margin hinv hv
  | worker ok => exact inv_workerStep P hP s ok hinv
  | dropTarget => exact inv_dropTarget P hP s hinv

theorem inv_reachable [DecidableEq D] (sys : Sys K V D P) (h : Reachable P H cap sys) :
    Inv P sys := by
  obtain ⟨n0, w, τ, h0, hs⟩ := h
  have hi := inv_init P hP n0 w h0
  clear h0
  generalize Sys.init P n0 w = s0 at hs hi
  induction hs with
  | refl => exact hi
  | cons hstep _ ih => exact ih (inv_step P H cap hP _ _ _ hi hstep)

end Lawful

end RightCash
