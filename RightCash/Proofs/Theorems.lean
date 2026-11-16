import RightCash.Proofs.Invariant

/-!
# The correctness theorems, for any lawful eviction policy

`refines`, `rootBinding`, `deterministicPropose`, `prefetchIndependent` and
`prefetchIndependentTraces` prove the propositions of `RightCash.Spec` for
every policy satisfying `Policy.Lawful`, every choice of hash functions and
every capacity. `RightCash.Main` instantiates them for FIFO and LRU-write.
-/

set_option linter.unusedSectionVars false

namespace RightCash

variable {K V D : Type} [DecidableEq K] [DecidableEq D]

section Lawful
variable (P : Policy K) (H : Hashes K V P.Cons D) (cap : Nat) (hP : P.Lawful)

/-! ## Internal actions leave the consensus projection unchanged -/

theorem proj_retarget (s : Sys K V D P) (i : Nat) : (s.retarget P i).proj P = s.proj P := rfl

theorem proj_hint (hP : P.Lawful) (s : Sys K V D P) (v : Nat) (ks : List K) (margin : Nat) :
    (s.hint P cap v ks margin).proj P = s.proj P := by
  unfold Sys.hint
  cases s.spec with
  | none => rfl
  | some tc =>
    obtain ⟨t, c⟩ := tc
    simp only
    split
    · rename_i ht
      subst ht
      simp only [Sys.proj, CSys.mk.injEq, and_true]
      funext i
      by_cases hi : i = t
      · subst hi; simp [fupd_same, Node.state, hP.hint_cons]
      · simp [fupd_ne _ _ hi]
    · rfl

theorem proj_prefetch (hP : P.Lawful) (s : Sys K V D P) (v : Nat) (ks : List K) (margin : Nat) :
    (s.prefetch P cap v ks margin).proj P = s.proj P := by
  unfold Sys.prefetch
  split
  · rw [proj_hint P cap hP]
    split <;> rfl
  · rfl

theorem proj_workerStep (s : Sys K V D P) (ok : Bool) : (s.workerStep P ok).proj P = s.proj P := by
  unfold Sys.workerStep
  cases s.spec with
  | none => rfl
  | some tc => obtain ⟨t, c⟩ := tc; simp only; split <;> rfl

theorem proj_commit (s : Sys K V D P) (n : Nat) :
    (s.commit P n).proj P = ({ s with head := n } : Sys K V D P).proj P := by
  unfold Sys.commit
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

/-! ## Simulation: one step of the engine is one step of the reference -/

include hP in
theorem proj_step (s s' : Sys K V D P) (l : Label K V) (hinv : Inv P s)
    (h : Step P H cap s l s') : CSys.step P H cap (s.proj P) l = some (s'.proj P) := by
  cases h with
  | propose p b md ok hp =>
    have hc := proposeOut_child P H cap hP s p b md ok hinv
    simp only [CSys.step]
    rw [ite_eq_left (show p < (s.proj P).size from hp)]
    simp only [Sys.proj, Sys.propose, Option.some.injEq, CSys.mk.injEq, and_true]
    funext i
    by_cases hi : i = s.size
    · subst hi; simp only [fupd_same]; rw [hc.1, hc.2.1, hc.2.2]
    · simp only [fupd_ne _ _ hi]
  | commit n hn hpar hroot =>
    rw [proj_commit]
    simp only [CSys.step]
    split
    · rfl
    · rename_i hneg; exact absurd ⟨hn, hpar, hroot⟩ hneg
  | prefetch v ks margin _ => rw [proj_prefetch P cap hP]; rfl
  | worker ok => rw [proj_workerStep]; rfl
  | dropTarget => rfl

include hP in
theorem run_steps (s s' : Sys K V D P) (τ : List (Label K V)) (hinv : Inv P s)
    (h : Steps P H cap s τ s') : CSys.run P H cap (s.proj P) τ = some (s'.proj P) := by
  induction h with
  | refl => rfl
  | cons hstep _ ih =>
    simp only [CSys.run]
    rw [proj_step P H cap hP _ _ _ hinv hstep]
    exact ih (inv_step P H cap hP _ _ _ hinv hstep)

/-- **Refinement**: every execution's consensus projection is the reference
run of its consensus actions. -/
theorem refines (hP : P.Lawful) : Refines P H cap :=
  fun n0 w _ _ h0 hs => run_steps P H cap hP _ _ _ (inv_init P hP n0 w h0) hs

/-- Internal actions do not matter to the reference run. -/
theorem run_consensusLabels (cs : CSys K V P.Cons D) (τ : List (Label K V)) :
    CSys.run P H cap cs τ = CSys.run P H cap cs (consensusLabels τ) := by
  induction τ generalizing cs with
  | nil => rfl
  | cons l τ ih =>
    cases l with
    | internal => exact ih cs
    | propose p b md =>
      show (CSys.step P H cap cs _).bind (fun cs' => CSys.run P H cap cs' τ) =
        (CSys.step P H cap cs _).bind (fun cs' => CSys.run P H cap cs' (consensusLabels τ))
      congr 1; funext cs'; exact ih cs'
    | commit n =>
      show (CSys.step P H cap cs _).bind (fun cs' => CSys.run P H cap cs' τ) =
        (CSys.step P H cap cs _).bind (fun cs' => CSys.run P H cap cs' (consensusLabels τ))
      congr 1; funext cs'; exact ih cs'

/-! ## The three properties -/

/-- **Property 3, functional form.** -/
theorem prefetchIndependent (hP : P.Lawful) : PrefetchIndependent P H cap := by
  intro sys sys' p b md hr h
  have hinv := inv_reachable P H cap hP sys hr
  cases h with
  | propose _ _ _ ok _ =>
    have hc := proposeOut_child P H cap hP sys p b md ok hinv
    show (fupd sys.nodes sys.size _ sys.size).state = _ ∧ (fupd sys.nodes sys.size _ sys.size).metaHash = _
    rw [fupd_same]
    exact ⟨hc.1, hc.2.1⟩

/-- **Property 3, two-instance form.** -/
theorem prefetchIndependentTraces (hP : P.Lawful) : PrefetchIndependentTraces P H cap := by
  intro n₁ n₂ w₁ w₂ τ₁ τ₂ sys₁ sys₂ h₁ h₂ hinit hs₁ hs₂ hτ
  have r₁ := refines P H cap hP n₁ w₁ τ₁ sys₁ h₁ hs₁
  have r₂ := refines P H cap hP n₂ w₂ τ₂ sys₂ h₂ hs₂
  rw [run_consensusLabels, hτ, hinit, ← run_consensusLabels] at r₁
  rw [r₁] at r₂
  exact Option.some.inj r₂

/-- **Property 1 (root binding).** Since R42 it needs neither reachability
nor the policy laws: every node's root, the initial node's included, hashes
its whole consensus state. -/
theorem rootBinding : RootBinding P H cap := by
  intro sys₁ sys₂ _ _ i j h
  exact rootOf_binding H cap _ _ _ _ h

/-- **Lookup by root (R43).** Holds for any nodes whatsoever. -/
theorem lookupBinding : LookupBinding P H cap := by
  intro n₁ n₂ r h₁ h₂
  classical
  by_cases hb : H.Broken
  · exact Or.inr hb
  left
  have nclaw : ∀ (x : RootPre D) (st : Store K V), H.root x ≠ H.storage st :=
    fun x st e => hb (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, st, e⟩))))
  have nst : ¬Collision H.storage := fun c => hb (Or.inr (Or.inr (Or.inr (Or.inl c))))
  rcases h₁ with e₁ | ⟨w₁, s₁⟩ <;> rcases h₂ with e₂ | ⟨w₂, s₂⟩
  · have hst := (rootOf_binding H cap _ _ _ _ (e₁.trans e₂.symm)).resolve_right hb
    exact ⟨fun k => by rw [hst], fun _ => hst⟩
  · exact absurd (e₁.trans s₂.symm) (nclaw _ _)
  · exact absurd (e₂.trans s₁.symm) (nclaw _ _)
  · have hs : n₁.store = n₂.store := eq_of_not_collision nst (s₁.trans s₂.symm)
    refine ⟨fun k => ?_, fun h => ?_⟩
    · simp [kvOf, Node.state, w₁ k, w₂ k, hs]
    · rcases h with e | e
      · exact absurd (e.trans s₁.symm) (nclaw _ _)
      · exact absurd (e.trans s₂.symm) (nclaw _ _)

/-- Storage roots are shared more widely than combined roots. An empty block
on a node whose write set is empty (the initial node of an opt-in, say)
yields a node with the same storage view, again with an empty write set, one
height up. Both answer to the same storage root (R43) and read identically
(`lookupBinding`), but their consensus states differ, and so, unless a hash is
broken, do their combined roots and those of any block proposed on them.
Assumption A7 rules this out (`lookupUnique`). -/
theorem emptyBlock_bareRoot (hP : P.Lawful) (sys sys' : Sys K V D P) (p : Nat)
    (md : Option (List UInt8)) (hr : Reachable P H cap sys) (hempty : ∀ k, (sys.nodes p).ws k = none)
    (h : Step P H cap sys (.propose p [] md) sys') :
    (sys'.nodes sys.size).AnswersTo P H cap (H.storage (sys.nodes p).store) ∧
    (sys.nodes p).AnswersTo P H cap (H.storage (sys.nodes p).store) ∧
    (sys'.nodes sys.size).state ≠ (sys.nodes p).state ∧
    ((sys'.nodes sys.size).root P H cap ≠ (sys.nodes p).root P H cap ∨ H.Broken) := by
  have hc := (prefetchIndependent P H cap hP sys sys' p [] md hr h).1
  have hn := (inv_reachable P H cap hP sys hr).node p
  have hv : ∀ k, k ∉ (P.specWrites (P.cons (sys.nodes p).pol) [] ((sys.nodes p).height + 1) cap).1 := by
    intro k hk
    rcases hP.victims_sub _ _ _ _ k hk with ht | hb
    · have := (hn.2.1 k).2 ht
      rw [hempty k] at this
      exact absurd this (by simp)
    · simp at hb
  have hws : ∀ k, (sys'.nodes sys.size).ws k = none := by
    intro k
    have := congrArg (fun st => st.ws k) hc
    simp only [Node.state, specPropose, childWS, List.map_nil] at this
    rw [this, ite_eq_right (hv k)]
    simp [finalEntries, batchFinal, hempty k, emptyMap]
  have hstore : (sys'.nodes sys.size).store = (sys.nodes p).store := by
    funext k
    have := congrArg (fun st => st.store k) hc
    simp only [Node.state, specPropose, List.map_nil] at this
    rw [this, ite_eq_right (hv k)]
  have hne : (sys'.nodes sys.size).state ≠ (sys.nodes p).state := by
    intro e
    have := congrArg EState.height (hc.symm.trans e)
    simp [specPropose, Node.state] at this
  refine ⟨Or.inr ⟨hws, by rw [hstore]⟩, Or.inr ⟨hempty, rfl⟩, hne, ?_⟩
  classical
  by_cases hb : H.Broken
  · exact Or.inr hb
  · exact Or.inl fun e => hne ((rootOf_binding H cap _ _ _ _ e).resolve_right hb)

/-- **Property 2 (deterministic transitions).** -/
theorem deterministicPropose (hP : P.Lawful) : DeterministicPropose P H cap := by
  intro sys₁ sys₂ sys₁' sys₂' p₁ p₂ b md hr₁ hr₂ hroot hs₁ hs₂
  rcases rootBinding P H cap sys₁ sys₂ hr₁ hr₂ p₁ p₂ hroot with heq | hbroken
  · obtain ⟨c₁, m₁⟩ := prefetchIndependent P H cap hP sys₁ sys₁' p₁ b md hr₁ hs₁
    obtain ⟨c₂, m₂⟩ := prefetchIndependent P H cap hP sys₂ sys₂' p₂ b md hr₂ hs₂
    have hst : (sys₁'.nodes sys₁.size).state = (sys₂'.nodes sys₂.size).state := by
      rw [c₁, c₂, heq]
    refine Or.inl ⟨hst, ?_⟩
    unfold Node.root
    rw [hst, m₁, m₂]
  · exact Or.inr hbroken

/-- Property 2 iterated: from nodes with equal roots, proposing the same
sequence of batches (each on the previous proposal) keeps the roots equal. -/
theorem deterministicPropose_root (hP : P.Lawful)
    (sys₁ sys₂ sys₁' sys₂' : Sys K V D P) (p₁ p₂ : Nat) (b : List (BatchOp K V))
    (md : Option (List UInt8)) (hr₁ : Reachable P H cap sys₁) (hr₂ : Reachable P H cap sys₂)
    (hroot : (sys₁.nodes p₁).root P H cap = (sys₂.nodes p₂).root P H cap)
    (hs₁ : Step P H cap sys₁ (.propose p₁ b md) sys₁')
    (hs₂ : Step P H cap sys₂ (.propose p₂ b md) sys₂') :
    (sys₁'.nodes sys₁.size).root P H cap = (sys₂'.nodes sys₂.size).root P H cap ∨ H.Broken := by
  rcases deterministicPropose P H cap hP _ _ _ _ _ _ _ _ hr₁ hr₂ hroot hs₁ hs₂ with h | h
  · exact Or.inl h.2
  · exact Or.inr h

end Lawful

end RightCash
