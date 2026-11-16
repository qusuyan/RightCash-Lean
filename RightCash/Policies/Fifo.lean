import RightCash.Policies.Common

/-!
# FIFO (`src/policy/fifo.rs`)

Evict in order of first insertion; a rewrite does not move a key. The model
follows the Rust code function by function; `Fifo.lawful` proves the facts
the engine proofs need.

Faithfulness notes:
* `index` is not stored: membership (`contains`) is read off the order.
* `marked`/`hinted_new_keys` (`BTreeSet`s) are lists used as sets.
* `reconcile`'s Rust closure removes each victim's mark as a side effect while
  filtering; victims are distinct, so this equals filtering against the
  marks before removal, as modelled.
-/

set_option linter.unusedSectionVars false

namespace RightCash
namespace Fifo

open Policies

variable {K : Type} [DecidableEq K]

/-- The Rust `Fifo<K>` struct (the low watermark is a parameter of `policy`). -/
structure St (K : Type) where
  /-- Consensus: `(insertion height, key)`, oldest first. -/
  order : List (Nat × K)
  /-- Local: the speculation high watermark. -/
  trigger : Option Nat
  /-- Local: outstanding predictions. -/
  marked : List K
  /-- Local: distinct hinted new keys this block. -/
  hintedNewKeys : List K
  /-- Local: whether this chain already selected its prefix. -/
  predictionStarted : Bool

/-- The consensus part of `writes`: new keys go to the back at `height`
(ties by key); on overflow, the oldest keys are drained down to `low`. -/
def specWrites (le : K → K → Bool) (low : Nat) (order : List (Nat × K)) (ks : List K)
    (height cap : Nat) : List K × List (Nat × K) :=
  let written := sortDedup le ks
  let newKeys := written.filter (fun k => k ∉ keysOf order)
  let order1 := order ++ newKeys.map (fun k => (height, k))
  evictPrefix le order1 (evictionCount low (order.length + newKeys.length) cap)

/-- `Fifo::reconcile`. -/
def reconcile (s : St K) (victims written : List K) : Prediction K × St K :=
  if victims = [] then
    (⟨written.filter (fun k => k ∈ s.marked), []⟩, { s with hintedNewKeys := [] })
  else
    (⟨victims.filter (fun k => k ∉ s.marked ∨ k ∈ written), s.marked.filter (fun k => k ∉ victims)⟩,
      { s with hintedNewKeys := [], predictionStarted := false,
               marked := s.marked.filter (fun k => k ∉ victims) })

/-- `Fifo::writes`. -/
def writes (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K) (height cap : Nat) :
    Eviction K × St K :=
  let r := specWrites le low s.order ks height cap
  let rc := reconcile { s with order := r.2 } r.1 (sortDedup le ks)
  (⟨r.1, rc.1.evict, rc.1.retract⟩, rc.2)

/-- `Fifo::hint_writes`: on the first trigger, predict the oldest
`capacity - low + margin` keys. -/
def hintWrites (low : Nat) (s : St K) (ks : List K) (cap margin : Nat) : Prediction K × St K :=
  if s.predictionStarted then (⟨[], []⟩, s)
  else
    let hinted := (ks.filter (fun k => k ∉ keysOf s.order)).foldl setInsert s.hintedNewKeys
    if s.order.length + hinted.length ≥ s.trigger.getD cap then
      let r := insertNew (keysOf (s.order.take ((cap - low) + margin))) s.marked
      (⟨r.1, []⟩, { s with predictionStarted := true, marked := r.2, hintedNewKeys := [] })
    else (⟨[], []⟩, { s with hintedNewKeys := hinted })

/-- `Fifo::reset_hints`. -/
def resetHints (s : St K) : St K :=
  { s with marked := [], hintedNewKeys := [], predictionStarted := false }

/-- FIFO with key comparison `le` and low watermark `low`, as a `Policy`. -/
def policy (le : K → K → Bool) (low : Nat) : Policy K where
  St := St K
  Cons := List (Nat × K)
  cons := St.order
  tracked := keysOf
  wf := fun o => (keysOf o).Nodup
  marked := St.marked
  fresh := []
  specWrites := specWrites le low
  writes := writes le low
  hintWrites := hintWrites low
  resetHints := resetHints
  predicted := St.marked

/-! ## Proofs -/

theorem reconcile_order (s : St K) (v w : List K) : (reconcile s v w).2.order = s.order := by
  unfold reconcile; split <;> rfl

theorem reconcile_marked (s : St K) (v w : List K) (k : K) (hk : k ∈ (reconcile s v w).2.marked) :
    k ∈ s.marked ∧ k ∉ v := by
  unfold reconcile at hk
  split at hk
  · rename_i hv; subst hv; exact ⟨hk, by simp⟩
  · simpa using hk

theorem hintWrites_order (low : Nat) (s : St K) (ks : List K) (cap margin : Nat) :
    (hintWrites low s ks cap margin).2.order = s.order := by
  unfold hintWrites
  split
  · rfl
  · simp only; split <;> rfl

/-- Keys of the order after appending a batch's new keys. -/
theorem mem_order1 (le : K → K → Bool) (order : List (Nat × K)) (ks : List K) (h : Nat) (k : K) :
    k ∈ keysOf (order ++ ((sortDedup le ks).filter (fun k => k ∉ keysOf order)).map (fun k => (h, k)))
      ↔ k ∈ keysOf order ∨ k ∈ ks := by
  rw [keysOf_append, keysOf_at, List.mem_append, List.mem_filter, mem_sortDedup]
  by_cases hk : k ∈ keysOf order <;> simp [hk]

theorem nodup_order1 (le : K → K → Bool) (order : List (Nat × K)) (ks : List K) (h : Nat)
    (hnd : (keysOf order).Nodup) :
    (keysOf (order ++ ((sortDedup le ks).filter (fun k => k ∉ keysOf order)).map
      (fun k => (h, k)))).Nodup := by
  rw [keysOf_append, keysOf_at, List.nodup_append]
  refine ⟨hnd, (nodup_sortDedup le ks).sublist List.filter_sublist, ?_⟩
  intro a ha b hb hab
  subst hab
  simp only [List.mem_filter, decide_eq_true_eq] at hb
  exact hb.2 ha

theorem writes_order (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K) (h cap : Nat) :
    (writes le low s ks h cap).2.order = (specWrites le low s.order ks h cap).2 := by
  unfold writes; simp only; rw [reconcile_order]

theorem tracked_spec (le : K → K → Bool) (low : Nat) (c : List (Nat × K)) (ks : List K)
    (h cap : Nat) (k : K) (hwf : (keysOf c).Nodup) :
    k ∈ keysOf (specWrites le low c ks h cap).2 ↔
      (k ∈ keysOf c ∨ k ∈ ks) ∧ k ∉ (specWrites le low c ks h cap).1 := by
  unfold specWrites
  simp only
  rw [mem_evictPrefix_rest le _ _ (nodup_order1 le c ks h hwf), mem_order1]

theorem victims_spec (le : K → K → Bool) (low : Nat) (c : List (Nat × K)) (ks : List K)
    (h cap : Nat) (k : K) (hk : k ∈ (specWrites le low c ks h cap).1) : k ∈ keysOf c ∨ k ∈ ks :=
  (mem_order1 le c ks h k).1 (victims_mem_order le _ _ hk)

theorem wf_spec (le : K → K → Bool) (low : Nat) (c : List (Nat × K)) (ks : List K)
    (h cap : Nat) (hwf : (keysOf c).Nodup) : (keysOf (specWrites le low c ks h cap).2).Nodup :=
  nodup_evictPrefix_rest le _ _ (nodup_order1 le c ks h hwf)

/-- `writes` on a block that evicts nothing. -/
theorem writes_kept (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K) (h cap : Nat)
    (hv : (specWrites le low s.order ks h cap).1 = []) :
    (writes le low s ks h cap).1.evict = (sortDedup le ks).filter (fun k => k ∈ s.marked) ∧
    (writes le low s ks h cap).1.retract = [] ∧
    (writes le low s ks h cap).2.marked = s.marked := by
  unfold writes reconcile
  simp only [hv]
  simp

/-- `writes` on an evicting block. -/
theorem writes_final (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K) (h cap : Nat)
    (hv : (specWrites le low s.order ks h cap).1 ≠ []) :
    (writes le low s ks h cap).1.evict =
      (specWrites le low s.order ks h cap).1.filter
        (fun k => k ∉ s.marked ∨ k ∈ sortDedup le ks) ∧
    (writes le low s ks h cap).1.retract =
      s.marked.filter (fun k => k ∉ (specWrites le low s.order ks h cap).1) ∧
    (writes le low s ks h cap).2.marked =
      s.marked.filter (fun k => k ∉ (specWrites le low s.order ks h cap).1) := by
  unfold writes reconcile
  simp only [hv]
  exact ⟨rfl, rfl, rfl⟩

theorem marked_spec (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K) (h cap : Nat)
    (hwf : (keysOf s.order).Nodup) (hmt : ∀ k ∈ s.marked, k ∈ keysOf s.order) :
    ∀ k ∈ (writes le low s ks h cap).2.marked, k ∈ keysOf (writes le low s ks h cap).2.order := by
  intro k hk
  obtain ⟨hm, hv⟩ := reconcile_marked _ _ _ k hk
  rw [writes_order]
  exact (tracked_spec le low s.order ks h cap k hwf).2 ⟨Or.inl (hmt k hm), hv⟩

theorem hint_marked_spec (low : Nat) (s : St K) (ks : List K) (cap margin : Nat)
    (hm : ∀ k ∈ s.marked, k ∈ keysOf s.order) :
    ∀ k ∈ (hintWrites low s ks cap margin).2.marked, k ∈ keysOf s.order := by
  intro k hk
  unfold hintWrites at hk
  split at hk
  · exact hm k hk
  · simp only at hk
    split at hk
    · rcases ((insertNew_spec _ _ k).1.1 hk) with h | h
      · exact hm k h
      · rw [keysOf_take] at h; exact List.mem_of_mem_take h
    · exact hm k hk

theorem hint_delta_spec (low : Nat) (s : St K) (ks : List K) (cap margin : Nat) :
    MarkDelta s.marked (hintWrites low s ks cap margin).2.marked
      (hintWrites low s ks cap margin).1.evict (hintWrites low s ks cap margin).1.retract := by
  intro k
  unfold hintWrites
  split
  · simp
  · simp only
    split
    · obtain ⟨h1, h2⟩ :=
        insertNew_spec (keysOf (s.order.take ((cap - low) + margin))) s.marked k
      refine ⟨fun h => absurd h List.not_mem_nil, fun _ he => h1.2 (Or.inr (h2.1 he).1),
        fun _ hne => ?_⟩
      rw [h1]
      constructor
      · rintro (h | h)
        · exact h
        · by_cases hm : k ∈ s.marked
          · exact hm
          · exact absurd (h2.2 ⟨h, hm⟩) hne
      · exact Or.inl
    · simp

theorem kept_spec (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K) (h cap : Nat)
    (hv : (specWrites le low s.order ks h cap).1 = []) :
    MarkDelta s.marked (writes le low s ks h cap).2.marked (writes le low s ks h cap).1.evict
        (writes le low s ks h cap).1.retract ∧
      ∀ k ∈ ks, k ∈ (writes le low s ks h cap).2.marked → k ∈ (writes le low s ks h cap).1.evict := by
  obtain ⟨he, hr, hm⟩ := writes_kept le low s ks h cap hv
  rw [he, hr, hm]
  refine ⟨fun k => ⟨by simp, fun _ hk => ?_, fun _ _ => Iff.rfl⟩, fun k hk hmk => ?_⟩
  · simp only [List.mem_filter, decide_eq_true_eq] at hk; exact hk.2
  · simp only [List.mem_filter, decide_eq_true_eq, mem_sortDedup]; exact ⟨hk, hmk⟩

theorem final_spec (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K) (h cap : Nat)
    (hv : (specWrites le low s.order ks h cap).1 ≠ []) :
    FinalOK s.marked ks (writes le low s ks h cap).1 := by
  obtain ⟨he, hr, _⟩ := writes_final le low s ks h cap hv
  unfold FinalOK
  rw [he, hr]
  change _ ∧ (∀ k ∈ (specWrites le low s.order ks h cap).1, _) ∧ _ ∧ _
  refine ⟨fun k hk => ?_, fun k hk hne => ?_, fun k hk hv' => ?_, fun k hk => ?_⟩
  · exact (List.mem_filter.1 hk).1
  · simp only [List.mem_filter, decide_eq_true_eq, mem_sortDedup, not_and] at hne
    have := hne hk
    by_cases hm : k ∈ s.marked
    · exact ⟨hm, fun hks => this (Or.inr hks)⟩
    · exact absurd (Or.inl hm) this
  · simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hk, hv'⟩
  · simp only [List.mem_filter, decide_eq_true_eq] at hk; exact hk.2

/-- **FIFO satisfies the policy laws.** -/
theorem lawful (le : K → K → Bool) (low : Nat) : (policy le low).Lawful where
  writes_victims _ _ _ _ := rfl
  writes_cons s ks h cap := writes_order le low s ks h cap
  hint_cons s ks cap margin := hintWrites_order low s ks cap margin
  reset_cons _ := rfl
  reset_marked _ := rfl
  predicted_eq _ := rfl
  wf_fresh := List.nodup_nil
  fresh_tracked := rfl
  wf_writes c ks h cap hwf := wf_spec le low c ks h cap hwf
  tracked_writes c ks h cap k hwf := tracked_spec le low c ks h cap k hwf
  victims_sub c ks h cap k hk := victims_spec le low c ks h cap k hk
  writes_marked s ks h cap hwf hmt := marked_spec le low s ks h cap hwf hmt
  hint_marked s ks cap margin hm := hint_marked_spec low s ks cap margin hm
  hint_delta s ks cap margin := hint_delta_spec low s ks cap margin
  kept_delta s ks h cap hv := kept_spec le low s ks h cap hv
  final s ks h cap hv := final_spec le low s ks h cap hv

/-- With a low watermark of at least 1, a block with a write never empties
the set (part of A7). -/
theorem keepsKey (le : K → K → Bool) (low : Nat) (hlow : 1 ≤ low) : (policy le low).KeepsKey := by
  intro (c : List (Nat × K)) ks h cap _ hks
  show keysOf (specWrites le low c ks h cap).2 ≠ []
  simp only [specWrites, evictPrefix, keysOf_drop]
  refine Policies.drop_evictionCount_ne_nil _ _ _ _ hlow (Nat.le_of_eq ?_) ?_
  · simp [keysOf]
  · have := Policies.written_pos le c ks hks
    simpa [keysOf] using this

end Fifo
end RightCash
