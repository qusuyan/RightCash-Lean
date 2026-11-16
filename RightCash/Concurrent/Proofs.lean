import RightCash.Concurrent.Model
import RightCash.Proofs.Theorems

/-!
# Correctness of the concurrent system

* `ainv_step`: every transition, by the writer, by the worker thread or by a
  dropped handle, preserves `AInv`. The key point is that the writer reasons
  about the *logical* chain (`logical chain queue`, the chain once the worker
  has drained the channel), which the worker's own steps never change up to
  `ChainSub`.
* `async_refines`: every concurrent execution's consensus projection is the
  reference run of its consensus actions, whatever the interleaving of the
  worker thread, the hints and the handle drops.
* `async_rootBinding`, `async_deterministicPropose`, `async_prefetchIndependent`,
  `async_prefetchIndependentTraces`: properties 1–3 for the concurrent system.
* `read_stable`, `read_specPropose`: what concurrent readers see. A node's
  read-visible data never changes after the node is created, so a read
  returns the value at its linearisation point (the registry lock), and reads
  behave like a key-value store to which batches are applied (eviction is
  invisible to readers).
-/

set_option linter.unusedSectionVars false

namespace RightCash

variable {K V D : Type} [DecidableEq K]

/-! ## The logical chain -/

/-- `d` is `c`, except that it may have failed since. -/
def ChainSub (d c : Chain K V) : Prop :=
  d.base = c.base ∧ (d.failed = false → c.failed = false ∧ ∀ k, d.eff k = c.eff k)

def OSub : Option (Chain K V) → Option (Chain K V) → Prop
  | some d, some c => ChainSub d c
  | none, none => True
  | _, _ => False

theorem chainSub_refl (c : Chain K V) : ChainSub c c := ⟨rfl, fun h => ⟨h, fun _ => rfl⟩⟩

theorem chainSub_submit (d c : Chain K V) (ops : List (SpecOp K V)) (h : ChainSub d c) :
    ChainSub (d.submit ops) (c.submit ops) := by
  refine ⟨by simp [h.1], fun hf => ?_⟩
  have hd : d.failed = false := by simpa using hf
  obtain ⟨hc, he⟩ := h.2 hd
  refine ⟨by simpa using hc, fun k => ?_⟩
  rw [Chain.eff_submit _ _ hd, Chain.eff_submit _ _ hc, he k, h.1]

theorem oSub_logical : ∀ (q : List (Req K V)) (od oc : Option (Chain K V)), OSub od oc →
    OSub (logical od q) (logical oc q)
  | [], _, _, h => h
  | r :: q, od, oc, h => by
    apply oSub_logical q
    cases r with
    | submit ops =>
      cases od <;> cases oc <;> simp [OSub, Req.process] at h ⊢
      exact chainSub_submit _ _ ops h
    | reset base => exact chainSub_refl _
    | finish ops md => trivial

theorem chainSub_build (c : Chain K V) : ChainSub c.build c :=
  ⟨rfl, fun h => ⟨h, fun k => Chain.eff_build c k⟩⟩

theorem chainSub_fail (c : Chain K V) : ChainSub c.fail c := ⟨rfl, fun h => by simp at h⟩

theorem logical_append (c : Option (Chain K V)) (q : List (Req K V)) (r : Req K V) :
    logical c (q ++ [r]) = Req.process (logical c q) r := by
  simp [logical, List.foldl_append]

section Proofs
variable (P : Policy K) (H : Hashes K V P.Cons D) (cap : Nat)

theorem chainOK_sub (n : Node K V D P) (c d : Chain K V) (hc : ChainOK P n c) (h : ChainSub d c) :
    ChainOK P n d := by
  refine ⟨h.1.trans hc.1, fun hf k => ?_⟩
  obtain ⟨hcf, he⟩ := h.2 hf
  rw [he k, hc.2 hcf k, h.1]

/-- `ChainOK` of the logical chain survives anything the worker does to the
actual chain (as long as it stays a "sub-chain"). -/
theorem logical_ok_transfer (n : Node K V D P) (q : List (Req K V)) (od oc : Option (Chain K V))
    (h : OSub od oc) (hok : ∀ c, logical oc q = some c → ChainOK P n c) :
    ∀ d, logical od q = some d → ChainOK P n d := by
  intro d hd
  have hs := oSub_logical q od oc h
  rw [hd] at hs
  cases hc : logical oc q with
  | none => rw [hc] at hs; cases hs
  | some c => rw [hc] at hs; exact chainOK_sub P n c d (hok c hc) hs

/-- The finish request a blocked propose waits on. -/
def finishReq (s : ASys K V D P) (pp : Pending K V) : Req K V :=
  .finish (specOps (finalEntries (s.nodes pp.p).ws pp.b) (writesOf P cap (s.nodes pp.p) pp.b).1.evict
    (writesOf P cap (s.nodes pp.p) pp.b).1.retract) pp.md

/-- The invariant of the concurrent system. -/
structure AInv (s : ASys K V D P) : Prop where
  node : ∀ i, NodeOK P (s.nodes i)
  noWorker : s.worker = false → s.target = none ∧ s.pending = none
  target_lt : ∀ t, s.target = some t → t < s.size
  chainOK : ∀ t, s.target = some t → ∀ c, logical s.chain s.queue = some c → ChainOK P (s.nodes t) c
  idle : s.pending = none → s.reply = none ∧ ∀ r ∈ s.queue, r.isFinish = false
  busy : ∀ pp, s.pending = some pp → s.target = none ∧ pp.p < s.size ∧
    (writesOf P cap (s.nodes pp.p) pp.b).1.victims ≠ [] ∧
    ((s.reply = none ∧ ∃ q, s.queue = q ++ [finishReq P cap s pp] ∧ (∀ r ∈ q, r.isFinish = false) ∧
        ∀ c, logical s.chain q = some c → ChainOK P (s.nodes pp.p) c) ∨
     (s.queue = [] ∧ ∃ r, s.reply = some r ∧
        ∀ st, r = some st → st = (specPropose P cap (s.nodes pp.p).state pp.b).store))

variable (hP : P.Lawful)
include hP

theorem ainv_init (n0 : Node K V D P) (w : Bool) (h0 : InitOK P n0) : AInv P cap (ASys.init P n0 w) := by
  have hi := inv_init P hP n0 w h0
  refine ⟨hi.node, fun hw => ?_, fun t ht => ?_, fun t ht c hc => ?_, fun _ => ⟨rfl, by simp [ASys.init]⟩,
    fun pp h => by simp [ASys.init] at h⟩
  · change w = false at hw; simp [ASys.init, hw]
  · simp only [ASys.init] at ht; split at ht
    · cases ht; exact Nat.zero_lt_one
    · cases ht
  · simp only [ASys.init] at ht hc
    split at ht
    · cases ht
      rename_i hw
      simp only [hw, ite_true, logical, List.foldl_nil, Option.some.injEq] at hc
      subst hc
      exact hi.chain 0 _ (by simp [Sys.init, hw])
    · cases ht

/-- Helper: the child of a `Propose` on `par` is well formed. -/
theorem endChild_ok (par : Node K V D P) (p : Nat) (b : List (BatchOp K V)) (md : Option (List UInt8))
    (r : Option (Store K V)) (hn : NodeOK P par) : NodeOK P (endChild P H cap par p b md r) := by
  unfold endChild
  cases r with
  | some st => exact mkChild_ok P H cap hP _ _ _ _ _ _ hn rfl (writes_marks_ok P cap hP par b hn)
  | none => exact plainChild_ok P H cap hP _ _ _ _ hn

theorem endChild_state (par : Node K V D P) (p : Nat) (b : List (BatchOp K V)) (md : Option (List UInt8))
    (r : Option (Store K V)) (hn : NodeOK P par)
    (hr : ∀ st, r = some st → st = (specPropose P cap par.state b).store) :
    (endChild P H cap par p b md r).state = specPropose P cap par.state b ∧
    (endChild P H cap par p b md r).metaHash = H.metadata md ∧
    (endChild P H cap par p b md r).parent = some p := by
  unfold endChild
  cases r with
  | some st => exact ⟨mkChild_state P H cap hP _ _ _ _ _ _ rfl (hr st rfl), rfl, rfl⟩
  | none => exact ⟨plainChild_state P H cap hP _ _ _ _ hn, rfl, rfl⟩

/-- Retargeting (after a step that keeps every other part of the invariant). -/
theorem ainv_retarget (s : ASys K V D P) (i : Nat) (hi : i < s.size) (hinv : AInv P cap s)
    (hidle : s.pending = none) : AInv P cap (s.retarget P i) := by
  unfold ASys.retarget
  split
  · rename_i hw
    refine ⟨hinv.node, fun h => by simp [hw] at h, fun t ht => ?_, fun t ht c hc => ?_, fun hp => ?_,
      fun pp hp => by rw [hidle] at hp; cases hp⟩
    · cases ht; exact hi
    · cases ht
      unfold logical at hc
      rw [List.foldl_append] at hc
      simp only [List.foldl_cons, List.foldl_nil, Req.process, Option.map_some, Option.some.injEq] at hc
      subst hc
      exact retargetChain_ok P hP _ (hinv.node _)
    · refine ⟨(hinv.idle hp).1, fun r hr => ?_⟩
      rcases List.mem_append.1 hr with hr | hr
      · exact (hinv.idle hp).2 r hr
      · simp at hr; rcases hr with rfl | rfl <;> rfl
  · exact hinv

theorem ainv_step [DecidableEq D] (s s' : ASys K V D P) (l : Label K V) (hinv : AInv P cap s)
    (h : AStep P H cap s l s') : AInv P cap s' := by
  cases h with
  | proposeNow p b md hidle hp hcond =>
    have hn := hinv.node p
    have hnodes : ∀ (c : Node K V D P), NodeOK P c → ∀ i, NodeOK P (fupd s.nodes s.size c i) := by
      intro c hc i; by_cases hi : i = s.size
      · subst hi; rw [fupd_same]; exact hc
      · rw [fupd_ne _ _ hi]; exact hinv.node i
    unfold ASys.proposeNow
    dsimp only
    split
    · rename_i ht
      have hV : (writesOf P cap (s.nodes p) b).1.victims = [] := by
        by_cases hv : (writesOf P cap (s.nodes p) b).1.victims = []
        · exact hv
        · exact absurd ⟨ht, hv⟩ hcond
      have hcOK := mkChild_ok P H cap hP (s.nodes p) p b md _ (s.nodes p).store hn rfl
        (writes_marks_ok P cap hP _ b hn)
      refine ⟨hnodes _ hcOK, fun hw => (by rw [(hinv.noWorker hw).1] at ht; cases ht),
        fun t ht' => (by cases ht'; exact Nat.lt_succ_self _), fun t ht' c hc => ?_,
        fun hp' => ⟨(hinv.idle hidle).1, fun r hr => ?_⟩, fun pp hp' => by simp [hidle] at hp'⟩
      · cases ht'
        show ChainOK P (fupd s.nodes s.size _ s.size) c
        rw [fupd_same]
        rw [logical_append] at hc
        cases hl : logical s.chain s.queue with
        | none => rw [hl] at hc; cases hc
        | some c0 =>
          rw [hl] at hc
          simp only [Req.process, Option.map_some, Option.some.injEq] at hc
          subst hc
          exact kept_chain_ok P H cap hP _ _ _ _ c0 hn (hinv.chainOK p ht c0 hl) hV
      · rcases List.mem_append.1 hr with hr | hr
        · exact (hinv.idle hidle).2 r hr
        · simp at hr; subst hr; rfl
    · have hcOK := plainChild_ok P H cap hP (s.nodes p) p b md hn
      refine ⟨hnodes _ hcOK, hinv.noWorker, fun t ht => Nat.lt_succ_of_lt (hinv.target_lt t ht),
        fun t ht c hc => ?_, hinv.idle, fun pp hp' => by simp [hidle] at hp'⟩
      show ChainOK P (fupd s.nodes s.size _ t) c
      rw [fupd_ne _ _ (Nat.ne_of_lt (hinv.target_lt t ht))]
      exact hinv.chainOK t ht c hc
  | proposeBegin p b md hidle hp ht hV =>
    refine ⟨hinv.node, fun hw => (by rw [(hinv.noWorker hw).1] at ht; cases ht),
      fun t ht' => (by cases ht'), fun t ht' => (by cases ht'), fun hp' => (by cases hp'), fun pp hp' => ?_⟩
    cases hp'
    refine ⟨rfl, hp, hV, Or.inl ⟨(hinv.idle hidle).1, s.queue, rfl, (hinv.idle hidle).2, ?_⟩⟩
    exact hinv.chainOK p ht
  | proposeEnd pp r hpend hrep =>
    obtain ⟨htn, hpl, hV, hcase⟩ := hinv.busy pp hpend
    have hq : s.queue = [] ∧ ∀ st, r = some st → st = (specPropose P cap (s.nodes pp.p).state pp.b).store := by
      rcases hcase with ⟨hr, _⟩ | ⟨hq, r', hr', hst⟩
      · rw [hrep] at hr; cases hr
      · rw [hrep] at hr'; cases hr'; exact ⟨hq, hst⟩
    have hn := hinv.node pp.p
    let s1 : ASys K V D P := { s with nodes := fupd s.nodes s.size (endChild P H cap (s.nodes pp.p) pp.p pp.b pp.md r), size := s.size + 1, pending := none, reply := none }
    have hinv1 : AInv P cap s1 := by
      refine ⟨fun i => ?_, fun hw => ⟨htn, rfl⟩, fun t ht => (by rw [htn] at ht; cases ht),
        fun t ht => (by rw [htn] at ht; cases ht), fun _ => ⟨rfl, (by simp [s1, hq.1])⟩, fun pp' h => (by cases h)⟩
      show NodeOK P (fupd s.nodes s.size _ i)
      by_cases hi : i = s.size
      · subst hi; rw [fupd_same]; exact endChild_ok P H cap hP _ _ _ _ _ hn
      · rw [fupd_ne _ _ hi]; exact hinv.node i
    exact ainv_retarget P cap hP s1 s.size (Nat.lt_succ_self _) hinv1 rfl
  | commit n hidle hn _ _ =>
    have h1 : AInv P cap { s with head := n } :=
      ⟨hinv.node, hinv.noWorker, hinv.target_lt, hinv.chainOK, hinv.idle, hinv.busy⟩
    unfold ASys.commit
    split
    · split
      · split
        · exact h1
        · exact ainv_retarget P cap hP _ n hn h1 hidle
      · exact ainv_retarget P cap hP _ n hn h1 hidle
    · exact h1
  | prefetch v ks margin hidle hv =>
    unfold ASys.prefetch
    split
    · have h1 : AInv P cap (if s.retargetCond P v then s.retarget P v else s) := by
        split
        · exact ainv_retarget P cap hP s v hv hinv hidle
        · exact hinv
      have hidle1 : (if s.retargetCond P v then s.retarget P v else s).pending = none := by
        split
        · unfold ASys.retarget; split <;> exact hidle
        · exact hidle
      generalize (if s.retargetCond P v then s.retarget P v else s) = s1 at h1 hidle1
      unfold ASys.hint
      split
      · rename_i ht
        have hn := h1.node v
        refine ⟨fun i => ?_, fun hw => ?_, h1.target_lt, fun t ht' c hc => ?_,
          fun hp' => ⟨(h1.idle hidle1).1, fun r hr => ?_⟩, fun pp hp' => by simp [hidle1] at hp'⟩
        · show NodeOK P (fupd s1.nodes v _ i)
          by_cases hi : i = v
          · subst hi; rw [fupd_same]; exact hinted_node_ok P cap hP _ ks margin hn
          · rw [fupd_ne _ _ hi]; exact h1.node i
        · exact h1.noWorker hw
        · rw [ht] at ht'; cases ht'
          show ChainOK P (fupd s1.nodes v _ v) c
          rw [fupd_same]
          rw [logical_append] at hc
          cases hl : logical s1.chain s1.queue with
          | none => rw [hl] at hc; cases hc
          | some c0 =>
            rw [hl] at hc
            simp only [Req.process, Option.map_some, Option.some.injEq] at hc
            subst hc
            exact hint_chain_ok P cap hP _ ks margin c0 hn (h1.chainOK v ht c0 hl)
        · rcases List.mem_append.1 hr with hr | hr
          · exact (h1.idle hidle1).2 r hr
          · simp at hr; subst hr; rfl
      · exact h1
    · exact hinv
  | dropTarget =>
    exact ⟨hinv.node, fun hw => ⟨rfl, (hinv.noWorker hw).2⟩, fun t ht => (by cases ht),
      fun t ht => (by cases ht), hinv.idle, fun pp hp => by
        obtain ⟨_, a, b, c⟩ := hinv.busy pp hp; exact ⟨rfl, a, b, c⟩⟩
  | dequeue r q ok hq =>
    have hlog : logical (s.dequeue P r q ok).chain (s.dequeue P r q ok).queue = logical s.chain s.queue := by
      rw [hq]; cases r <;> rfl
    refine ⟨?_, ?_, ?_, fun t ht c hc => ?_, fun hp => ?_, fun pp hp => ?_⟩
    · cases r <;> exact hinv.node
    · cases r <;> exact hinv.noWorker
    · cases r <;> exact hinv.target_lt
    · have ht' : s.target = some t := by cases r <;> exact ht
      rw [hlog] at hc
      have := hinv.chainOK t ht' c hc
      cases r <;> exact this
    · have hp' : s.pending = none := by cases r <;> exact hp
      obtain ⟨hr, hnf⟩ := hinv.idle hp'
      have hnf' : r.isFinish = false := hnf r (by rw [hq]; exact List.mem_cons_self ..)
      cases r with
      | submit ops => exact ⟨hr, fun r' hr' => hnf r' (by rw [hq]; exact List.mem_cons_of_mem _ hr')⟩
      | reset base => exact ⟨hr, fun r' hr' => hnf r' (by rw [hq]; exact List.mem_cons_of_mem _ hr')⟩
      | finish ops md => simp [Req.isFinish] at hnf'
    · have hp' : s.pending = some pp := by cases r <;> exact hp
      obtain ⟨htn, hpl, hV, hcase⟩ := hinv.busy pp hp'
      rcases hcase with ⟨hr, q0, hq0, hnf, hok⟩ | ⟨hq', _⟩
      · rw [hq] at hq0
        cases q0 with
        | nil =>
          -- the finish itself is handled now
          simp only [List.nil_append, List.cons.injEq] at hq0
          obtain ⟨rfl, rfl⟩ := hq0
          refine ⟨htn, hpl, hV, Or.inr ⟨rfl, _, rfl, fun st hst => ?_⟩⟩
          cases hc : s.chain with
          | none => rw [hc] at hst; cases hst
          | some c =>
            rw [hc] at hst
            exact finish_store P cap hP (s.nodes pp.p) pp.b pp.md ok c st (hinv.node pp.p)
              (hok c (by simp [logical, hc])) hV hst
        | cons r0 q1 =>
          simp only [List.cons_append, List.cons.injEq] at hq0
          obtain ⟨rfl, rfl⟩ := hq0
          have hnf0 : r.isFinish = false := hnf r (List.mem_cons_self ..)
          have hq1 : ∀ r' ∈ q1, r'.isFinish = false := fun r' hr' => hnf r' (List.mem_cons_of_mem _ hr')
          cases r with
          | finish _ _ => simp [Req.isFinish] at hnf0
          | submit ops => exact ⟨htn, hpl, hV, Or.inl ⟨hr, q1, rfl, hq1, fun c hc => hok c hc⟩⟩
          | reset base => exact ⟨htn, hpl, hV, Or.inl ⟨hr, q1, rfl, hq1, fun c hc => hok c hc⟩⟩
      · rw [hq] at hq'; cases hq'
  | build c ok hc hf hne =>
    have hsub : OSub (some (if ok then c.build else c.fail)) s.chain := by
      rw [hc]; cases ok
      · exact chainSub_fail c
      · exact chainSub_build c
    refine ⟨hinv.node, hinv.noWorker, hinv.target_lt, fun t ht d hd => ?_, hinv.idle, fun pp hp => ?_⟩
    · exact logical_ok_transfer P _ s.queue _ _ hsub (hinv.chainOK t ht) d hd
    · obtain ⟨htn, hpl, hV, hcase⟩ := hinv.busy pp hp
      refine ⟨htn, hpl, hV, ?_⟩
      rcases hcase with ⟨hr, q0, hq0, hnf, hok⟩ | h2
      · exact Or.inl ⟨hr, q0, hq0, hnf, logical_ok_transfer P _ q0 _ _ hsub hok⟩
      · exact Or.inr h2

/-! ## Refinement -/

theorem aproj_retarget (s : ASys K V D P) (i : Nat) : (s.retarget P i).proj P = s.proj P := by
  unfold ASys.retarget; split <;> rfl

theorem aproj_step [DecidableEq D] (s s' : ASys K V D P) (l : Label K V) (hinv : AInv P cap s)
    (h : AStep P H cap s l s') : CSys.step P H cap (s.proj P) l = some (s'.proj P) := by
  cases h with
  | proposeNow p b md hidle hp hcond =>
    have hn := hinv.node p
    simp only [CSys.step]
    rw [ite_eq_left (show p < (s.proj P).size from hp)]
    unfold ASys.proposeNow
    dsimp only
    have hchild : ∀ (c : Node K V D P), c.state = specPropose P cap (s.nodes p).state b →
        c.metaHash = H.metadata md → c.parent = some p →
        some ({ s.proj P with
          nodes := fupd (s.proj P).nodes (s.proj P).size ⟨specPropose P cap ((s.proj P).nodes p).state b,
            H.metadata md, some p⟩, size := (s.proj P).size + 1 } : CSys K V P.Cons D) =
          some ({ nodes := fun i => ⟨(fupd s.nodes s.size c i).state, (fupd s.nodes s.size c i).metaHash,
            (fupd s.nodes s.size c i).parent⟩, size := s.size + 1, head := s.head } : CSys K V P.Cons D) := by
      intro c h1 h2 h3
      simp only [ASys.proj, Option.some.injEq, CSys.mk.injEq, and_true]
      funext i
      by_cases hi : i = s.size
      · subst hi; simp only [fupd_same]; rw [h1, h2, h3]
      · simp only [fupd_ne _ _ hi]
    split
    · rename_i ht
      have hV : (writesOf P cap (s.nodes p) b).1.victims = [] := by
        by_cases hv : (writesOf P cap (s.nodes p) b).1.victims = []
        · exact hv
        · exact absurd ⟨ht, hv⟩ hcond
      apply hchild _ _ rfl rfl
      apply mkChild_state P H cap hP _ _ _ _ _ _ rfl
      rw [specPropose_store P cap hP, hV]; funext k; simp
    · exact hchild _ (plainChild_state P H cap hP _ _ _ _ hn) rfl rfl
  | proposeBegin p b md _ _ _ _ => rfl
  | proposeEnd pp r hpend hrep =>
    obtain ⟨_, hpl, _, hcase⟩ := hinv.busy pp hpend
    have hr : ∀ st, r = some st → st = (specPropose P cap (s.nodes pp.p).state pp.b).store := by
      rcases hcase with ⟨hr, _⟩ | ⟨_, r', hr', hst⟩
      · rw [hrep] at hr; cases hr
      · rw [hrep] at hr'; cases hr'; exact hst
    obtain ⟨c1, c2, c3⟩ := endChild_state P H cap hP (s.nodes pp.p) pp.p pp.b pp.md r (hinv.node pp.p) hr
    unfold ASys.proposeEnd
    rw [aproj_retarget P hP]
    simp only [CSys.step]
    rw [ite_eq_left (show pp.p < (s.proj P).size from hpl)]
    simp only [ASys.proj, Option.some.injEq, CSys.mk.injEq, and_true]
    funext i
    by_cases hi : i = s.size
    · subst hi; simp only [fupd_same]; rw [c1, c2, c3]
    · simp only [fupd_ne _ _ hi]
  | commit n _ hn hpar hroot =>
    have hc : (s.commit P n).proj P = ({ s with head := n } : ASys K V D P).proj P := by
      unfold ASys.commit
      split
      · split
        · split
          · rfl
          · exact aproj_retarget P hP _ n
        · exact aproj_retarget P hP _ n
      · rfl
    rw [hc]
    simp only [CSys.step]
    split
    · rfl
    · rename_i hneg; exact absurd ⟨hn, hpar, hroot⟩ hneg
  | prefetch v ks margin _ _ =>
    have h1 : (s.prefetch P cap v ks margin).proj P = s.proj P := by
      unfold ASys.prefetch
      split
      · have h0 : (if s.retargetCond P v then s.retarget P v else s).proj P = s.proj P := by
          split
          · exact aproj_retarget P hP s v
          · rfl
        generalize (if s.retargetCond P v then s.retarget P v else s) = s1 at h0
        rw [← h0]
        unfold ASys.hint
        split
        · rename_i ht
          simp only [ASys.proj, CSys.mk.injEq, and_true]
          funext i
          by_cases hi : i = v
          · subst hi; simp [fupd_same, Node.state, hP.hint_cons]
          · simp [fupd_ne _ _ hi]
        · rfl
      · rfl
    rw [h1]; rfl
  | dropTarget => rfl
  | dequeue r q ok _ => cases r <;> rfl
  | build c ok _ _ _ => rfl

theorem arun_steps [DecidableEq D] (s s' : ASys K V D P) (τ : List (Label K V)) (hinv : AInv P cap s)
    (h : ASteps P H cap s τ s') : CSys.run P H cap (s.proj P) τ = some (s'.proj P) ∧ AInv P cap s' := by
  induction h with
  | refl => exact ⟨rfl, hinv⟩
  | cons hstep _ ih =>
    obtain ⟨ih1, ih2⟩ := ih (ainv_step P H cap hP _ _ _ hinv hstep)
    refine ⟨?_, ih2⟩
    simp only [CSys.run]
    rw [aproj_step P H cap hP _ _ _ hinv hstep]
    exact ih1

/-- **Refinement, concurrent system.** -/
theorem async_refines [DecidableEq D] (n0 : Node K V D P) (w : Bool) (τ : List (Label K V))
    (s : ASys K V D P) (h0 : InitOK P n0) (hs : ASteps P H cap (ASys.init P n0 w) τ s) :
    CSys.run P H cap ((ASys.init P n0 w).proj P) τ = some (s.proj P) :=
  (arun_steps P H cap hP _ _ _ (ainv_init P cap hP n0 w h0) hs).1

theorem ainv_reachable [DecidableEq D] (s : ASys K V D P) (h : AReachable P H cap s) : AInv P cap s := by
  obtain ⟨n0, w, τ, h0, hs⟩ := h
  exact (arun_steps P H cap hP _ _ _ (ainv_init P cap hP n0 w h0) hs).2

/-! ## The three properties, concurrently -/

/-- **Property 1** for the concurrent system. -/
theorem async_rootBinding [DecidableEq D] (s₁ s₂ : ASys K V D P) (_h₁ : AReachable P H cap s₁)
    (_h₂ : AReachable P H cap s₂) (i j : Nat)
    (h : (s₁.nodes i).root P H cap = (s₂.nodes j).root P H cap) :
    (s₁.nodes i).state = (s₂.nodes j).state ∨ H.Broken :=
  rootOf_binding H cap _ _ _ _ h

/-- The node a `propose` step creates has the reference state. -/
theorem async_propose_child [DecidableEq D] (s s' : ASys K V D P) (p : Nat) (b : List (BatchOp K V))
    (md : Option (List UInt8)) (hinv : AInv P cap s) (h : AStep P H cap s (.propose p b md) s') :
    (s'.nodes s.size).state = specPropose P cap (s.nodes p).state b ∧
      (s'.nodes s.size).metaHash = H.metadata md := by
  have hstep := aproj_step P H cap hP _ _ _ hinv h
  have hp : p < s.size := by
    cases h with
    | proposeNow _ _ _ _ hp _ => exact hp
    | proposeEnd pp r hpend _ => exact (hinv.busy pp hpend).2.1
  simp only [CSys.step] at hstep
  rw [ite_eq_left (show p < (s.proj P).size from hp), Option.some.injEq] at hstep
  have := congrArg (fun cs : CSys K V P.Cons D => cs.nodes s.size) hstep
  simp only [ASys.proj, fupd_same] at this
  exact ⟨(congrArg CNode.state this).symm, (congrArg CNode.metaHash this).symm⟩

/-- **Property 3 (functional form)** for the concurrent system. -/
theorem async_prefetchIndependent [DecidableEq D] (s s' : ASys K V D P) (p : Nat)
    (b : List (BatchOp K V)) (md : Option (List UInt8)) (hr : AReachable P H cap s)
    (h : AStep P H cap s (.propose p b md) s') :
    (s'.nodes s.size).state = specPropose P cap (s.nodes p).state b ∧
      (s'.nodes s.size).metaHash = H.metadata md :=
  async_propose_child P H cap hP s s' p b md (ainv_reachable P H cap hP s hr) h

/-- **Property 2** for the concurrent system. -/
theorem async_deterministicPropose [DecidableEq D] (s₁ s₂ s₁' s₂' : ASys K V D P) (p₁ p₂ : Nat)
    (b : List (BatchOp K V)) (md : Option (List UInt8))
    (hr₁ : AReachable P H cap s₁) (hr₂ : AReachable P H cap s₂)
    (hroot : (s₁.nodes p₁).root P H cap = (s₂.nodes p₂).root P H cap)
    (h₁ : AStep P H cap s₁ (.propose p₁ b md) s₁') (h₂ : AStep P H cap s₂ (.propose p₂ b md) s₂') :
    ((s₁'.nodes s₁.size).state = (s₂'.nodes s₂.size).state ∧
      (s₁'.nodes s₁.size).root P H cap = (s₂'.nodes s₂.size).root P H cap) ∨ H.Broken := by
  rcases async_rootBinding P H cap hP s₁ s₂ hr₁ hr₂ p₁ p₂ hroot with heq | hb
  · obtain ⟨c₁, m₁⟩ := async_prefetchIndependent P H cap hP s₁ s₁' p₁ b md hr₁ h₁
    obtain ⟨c₂, m₂⟩ := async_prefetchIndependent P H cap hP s₂ s₂' p₂ b md hr₂ h₂
    have hst : (s₁'.nodes s₁.size).state = (s₂'.nodes s₂.size).state := by rw [c₁, c₂, heq]
    refine Or.inl ⟨hst, ?_⟩
    unfold Node.root; rw [hst, m₁, m₂]
  · exact Or.inr hb

/-- **Property 3 (two-instance form)** for the concurrent system: the same
consensus actions under any two schedules of the worker threads, hints and
handle drops give the same consensus state. -/
theorem async_prefetchIndependentTraces [DecidableEq D] (n₁ n₂ : Node K V D P) (w₁ w₂ : Bool)
    (τ₁ τ₂ : List (Label K V)) (s₁ s₂ : ASys K V D P) (h₁ : InitOK P n₁) (h₂ : InitOK P n₂)
    (hinit : (ASys.init P n₁ w₁).proj P = (ASys.init P n₂ w₂).proj P)
    (hs₁ : ASteps P H cap (ASys.init P n₁ w₁) τ₁ s₁) (hs₂ : ASteps P H cap (ASys.init P n₂ w₂) τ₂ s₂)
    (hτ : consensusLabels τ₁ = consensusLabels τ₂) : s₁.proj P = s₂.proj P := by
  have r₁ := async_refines P H cap hP n₁ w₁ τ₁ s₁ h₁ hs₁
  have r₂ := async_refines P H cap hP n₂ w₂ τ₂ s₂ h₂ hs₂
  rw [run_consensusLabels, hτ, hinit, ← run_consensusLabels] at r₁
  rw [r₁] at r₂
  exact Option.some.inj r₂

/-! ## Readers -/

/-- One reference step never changes an existing node. -/
theorem csys_step_old [DecidableEq D] (cs cs' : CSys K V P.Cons D) (l : Label K V)
    (h : CSys.step P H cap cs l = some cs') : cs.size ≤ cs'.size ∧ ∀ i < cs.size, cs'.nodes i = cs.nodes i := by
  cases l with
  | propose p b md =>
    simp only [CSys.step] at h
    split at h
    · cases h; exact ⟨Nat.le_succ _, fun i hi => fupd_ne _ _ (Nat.ne_of_lt hi)⟩
    · cases h
  | commit n =>
    simp only [CSys.step] at h
    split at h
    · cases h; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
    · cases h
  | internal => simp only [CSys.step, Option.some.injEq] at h; subst h; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩

/-- **Reads are stable.** Whatever runs concurrently (writer operations,
hints from any number of sources, the worker thread, dropped handles), a
node's consensus state, and hence every read through it, never changes once
the node exists. A read is therefore linearisable at the moment it resolves
its node under the registry lock. -/
theorem read_stable [DecidableEq D] (s s' : ASys K V D P) (τ : List (Label K V)) (hinv : AInv P cap s)
    (h : ASteps P H cap s τ s') :
    s.size ≤ s'.size ∧ ∀ i < s.size, (s'.nodes i).state = (s.nodes i).state ∧
      ∀ k, kvOf P (s'.nodes i).state k = kvOf P (s.nodes i).state k := by
  induction h with
  | refl => exact ⟨Nat.le_refl _, fun _ _ => ⟨rfl, fun _ => rfl⟩⟩
  | @cons s0 s1 s2 l τ hstep _ ih =>
    obtain ⟨ih1, ih2⟩ := ih (ainv_step P H cap hP _ _ _ hinv hstep)
    obtain ⟨hsz, hold⟩ := csys_step_old P H cap hP _ _ l (aproj_step P H cap hP _ _ _ hinv hstep)
    refine ⟨Nat.le_trans hsz ih1, fun i hi => ?_⟩
    have h1 := congrArg CNode.state (hold i hi)
    have h2 := (ih2 i (Nat.lt_of_lt_of_le hi hsz)).1
    have hst : (s2.nodes i).state = (s0.nodes i).state := h2.trans h1
    exact ⟨hst, fun k => by rw [hst]⟩

/-- **Eviction is invisible to readers**: after `Propose(b)`, a key reads
as the batch's last write to it, or else exactly as before. -/
theorem read_specPropose (st : EState K V P.Cons) (b : List (BatchOp K V))
    (hdom : ∀ k, (st.ws k).isSome ↔ k ∈ P.tracked st.policy) (k : K) :
    kvOf P (specPropose P cap st b) k = (batchFinal b k).elim (kvOf P st k) Entry.toStore := by
  unfold kvOf specPropose childWS
  dsimp only
  generalize hr : P.specWrites st.policy (b.map BatchOp.key) (st.height + 1) cap = r
  by_cases hv : k ∈ r.1
  · rw [ite_eq_left hv, ite_eq_left hv]
    have hin : k ∈ P.tracked st.policy ∨ k ∈ b.map BatchOp.key := hP.victims_sub _ _ _ _ k (by rw [hr]; exact hv)
    unfold finalEntries
    cases hb : batchFinal b k with
    | some e => rfl
    | none =>
      have : k ∈ P.tracked st.policy := by
        rcases hin with h | h
        · exact h
        · exact absurd ((batchFinal_isSome b k).2 h) (by rw [hb]; simp)
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 ((hdom k).2 this)
      simp [he]
  · rw [ite_eq_right hv, ite_eq_right hv]
    unfold finalEntries
    cases hb : batchFinal b k with
    | some e => rfl
    | none => simp

end Proofs

end RightCash
