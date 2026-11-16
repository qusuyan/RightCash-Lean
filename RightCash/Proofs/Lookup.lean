import RightCash.Proofs.Theorems
import RightCash.Concurrent.Proofs

/-!
# Lookup by root under assumption A7

`Revision(root)` resolves a node by its combined root, or by its storage
view's root while its write set is empty (R43). `lookupBinding` shows that
all nodes answering to one root read identically, but nodes sharing a storage
root can differ in consensus state (`emptyBlock_bareRoot`).

Under A7 (every batch writes at least one key, and the policy keeps a key
after such a batch, `Policy.KeepsKey`), no node but the initial one ever has
an empty write set. The proof is an invariant of the reference semantics
`CSys.run` (`CInv`), so it carries over to the engine through `refines` and to
the concurrent system through `async_refines`.
-/

set_option linter.unusedSectionVars false

namespace RightCash

variable {K V D : Type} [DecidableEq K] [DecidableEq D]

section Lookup
variable (P : Policy K) (H : Hashes K V P.Cons D) (cap : Nat)

/-- The consensus half of `NodeOK`: the policy's state is well formed and
tracks exactly the write set's keys. -/
def StateOK (st : EState K V P.Cons) : Prop :=
  P.wf st.policy ∧ ∀ k, (st.ws k).isSome ↔ k ∈ P.tracked st.policy

/-- Invariant of the reference semantics: every node is consistent, and
every node but the initial one has a nonempty write set. -/
def CInv (cs : CSys K V P.Cons D) : Prop :=
  ∀ i < cs.size, StateOK P (cs.nodes i).state ∧ (0 < i → ∃ k, ((cs.nodes i).state.ws k).isSome)

theorem specPropose_ok (hP : P.Lawful) (st : EState K V P.Cons) (b : List (BatchOp K V))
    (h : StateOK P st) : StateOK P (specPropose P cap st b) := by
  refine ⟨hP.wf_writes _ _ _ _ h.1, fun k => ?_⟩
  unfold specPropose
  dsimp only
  rw [hP.tracked_writes _ _ _ _ _ h.1]
  unfold childWS
  by_cases hV : k ∈ (P.specWrites st.policy (b.map BatchOp.key) (st.height + 1) cap).1
  · simp [hV]
  · rw [ite_eq_right hV, finalEntries_isSome, h.2 k]
    simp only [hV, not_false_eq_true, and_true]
    exact Or.comm

/-- Under `KeepsKey`, a batch with a write leaves a nonempty write set. -/
theorem specPropose_nonempty (hP : P.Lawful) (hK : P.KeepsKey) (st : EState K V P.Cons)
    (b : List (BatchOp K V)) (h : StateOK P st) (hb : b ≠ []) :
    ∃ k, ((specPropose P cap st b).ws k).isSome := by
  have hc := specPropose_ok P cap hP st b h
  have hne := hK st.policy (b.map BatchOp.key) (st.height + 1) cap h.1 (by simpa using hb)
  obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ hne
  exact ⟨k, (hc.2 k).2 hk⟩

theorem cinv_step (hP : P.Lawful) (hK : P.KeepsKey) (cs cs' : CSys K V P.Cons D) (l : Label K V)
    (hl : l.Writes) (hinv : CInv P cs) (h : CSys.step P H cap cs l = some cs') : CInv P cs' := by
  cases l with
  | propose p b md =>
    simp only [CSys.step] at h
    split at h
    · rename_i hp
      cases h
      intro i hi
      by_cases hix : i = cs.size
      · subst hix
        simp only [fupd_same]
        have hpar := (hinv p hp).1
        exact ⟨specPropose_ok P cap hP _ b hpar, fun _ => specPropose_nonempty P cap hP hK _ b hpar hl⟩
      · simp only [fupd_ne _ _ hix]
        exact hinv i (by simp only at hi; omega)
    · cases h
  | commit n =>
    simp only [CSys.step] at h
    split at h
    · cases h; exact hinv
    · cases h
  | internal =>
    simp only [CSys.step] at h
    cases h; exact hinv

theorem cinv_run (hP : P.Lawful) (hK : P.KeepsKey) :
    ∀ (τ : List (Label K V)) (cs cs' : CSys K V P.Cons D), CInv P cs → (∀ l ∈ τ, l.Writes) →
      CSys.run P H cap cs τ = some cs' → CInv P cs'
  | [], cs, cs', h, _, hr => by
    simp only [CSys.run, Option.some.injEq] at hr
    subst hr; exact h
  | l :: τ, cs, cs', h, hw, hr => by
    simp only [CSys.run] at hr
    cases hs : CSys.step P H cap cs l with
    | none => rw [hs] at hr; cases hr
    | some cs1 =>
      rw [hs] at hr
      exact cinv_run hP hK τ cs1 cs'
        (cinv_step P H cap hP hK cs cs1 l (hw l (List.mem_cons_self ..)) h hs)
        (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) hr

/-- The initial node (marks reset) is consistent. -/
theorem stateOK_init (hP : P.Lawful) (n0 : Node K V D P) (h0 : InitOK P n0) :
    StateOK P ({ n0 with pol := P.resetHints n0.pol, parent := none } : Node K V D P).state := by
  have hc := hP.reset_cons n0.pol
  refine ⟨?_, fun k => ?_⟩
  · show P.wf (P.cons (P.resetHints n0.pol)); rw [hc]; exact h0.1
  · show _ ↔ k ∈ P.tracked (P.cons (P.resetHints n0.pol)); rw [hc]; exact h0.2 k

theorem cinv_single (cs : CSys K V P.Cons D) (h1 : cs.size = 1) (h0 : StateOK P (cs.nodes 0).state) :
    CInv P cs := by
  intro i hi
  have : i = 0 := by omega
  subst this
  exact ⟨h0, fun h => absurd h (Nat.lt_irrefl 0)⟩

/-- Among nodes where only node 0 may have an empty write set, two nodes that
answer to the same root have the same consensus state, or a hash is broken. -/
theorem answers_unique (nodes : Nat → Node K V D P) (size : Nat)
    (hne : ∀ i, 0 < i → i < size → ∃ k, ((nodes i).ws k).isSome)
    (i j : Nat) (r : D) (hi : i < size) (hj : j < size)
    (h₁ : (nodes i).AnswersTo P H cap r) (h₂ : (nodes j).AnswersTo P H cap r) :
    (nodes i).state = (nodes j).state ∨ H.Broken := by
  classical
  by_cases hb : H.Broken
  · exact Or.inr hb
  left
  have nclaw : ∀ (x : RootPre D) (st : Store K V), H.root x ≠ H.storage st :=
    fun x st e => hb (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, st, e⟩))))
  have zero : ∀ m, m < size → (∀ k, (nodes m).ws k = none) → m = 0 := by
    intro m hm he
    by_cases h0 : m = 0
    · exact h0
    · obtain ⟨k, hk⟩ := hne m (Nat.pos_of_ne_zero h0) hm
      rw [he k] at hk
      simp at hk
  rcases h₁ with e₁ | ⟨w₁, s₁⟩ <;> rcases h₂ with e₂ | ⟨w₂, s₂⟩
  · exact (rootOf_binding H cap _ _ _ _ (e₁.trans e₂.symm)).resolve_right hb
  · exact absurd (e₁.trans s₂.symm) (nclaw _ _)
  · exact absurd (e₂.trans s₁.symm) (nclaw _ _)
  · rw [zero i hi w₁, zero j hj w₂]

/-- Under A7, only the initial node of an engine can have an empty write set. -/
theorem nonempty_of_writes (hP : P.Lawful) (hK : P.KeepsKey) (n0 : Node K V D P) (w : Bool)
    (τ : List (Label K V)) (sys : Sys K V D P) (h0 : InitOK P n0)
    (hs : Steps P H cap (Sys.init P n0 w) τ sys) (hw : ∀ l ∈ τ, l.Writes) :
    ∀ i, 0 < i → i < sys.size → ∃ k, ((sys.nodes i).ws k).isSome := by
  have hc : CInv P (sys.proj P) :=
    cinv_run P H cap hP hK τ _ _ (cinv_single P _ rfl (stateOK_init P hP n0 h0)) hw
      (refines P H cap hP n0 w τ sys h0 hs)
  exact fun i hi hs => (hc i hs).2 hi

/-- **R43 under A7**: lookup by root is unambiguous within an engine. -/
theorem lookupUnique (hP : P.Lawful) (hK : P.KeepsKey) : LookupUnique P H cap := by
  intro n0 w τ sys h0 hs hw i j r hi hj h₁ h₂
  exact answers_unique P H cap sys.nodes sys.size (nonempty_of_writes P H cap hP hK n0 w τ sys h0 hs hw)
    i j r hi hj h₁ h₂

/-- The same for the concurrent system (worker thread, channel, concurrent
hints), through `async_refines`. -/
theorem async_lookupUnique (hP : P.Lawful) (hK : P.KeepsKey) (n0 : Node K V D P) (w : Bool)
    (τ : List (Label K V)) (s : ASys K V D P) (h0 : InitOK P n0)
    (hs : ASteps P H cap (ASys.init P n0 w) τ s) (hw : ∀ l ∈ τ, l.Writes)
    (i j : Nat) (r : D) (hi : i < s.size) (hj : j < s.size)
    (h₁ : (s.nodes i).AnswersTo P H cap r) (h₂ : (s.nodes j).AnswersTo P H cap r) :
    (s.nodes i).state = (s.nodes j).state ∨ H.Broken := by
  have hc : CInv P (s.proj P) :=
    cinv_run P H cap hP hK τ _ _ (cinv_single P _ rfl (stateOK_init P hP n0 h0)) hw
      (async_refines P H cap hP n0 w τ s h0 hs)
  exact answers_unique P H cap s.nodes s.size (fun m hm hms => (hc m hms).2 hm) i j r hi hj h₁ h₂

end Lookup

end RightCash
