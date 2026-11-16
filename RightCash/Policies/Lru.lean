import RightCash.Policies.Common

/-!
# LRU by write (`src/policy/lru_write.rs`)

Evict the key whose last write is oldest; every write moves its key to the
back. Hints withdraw predictions for keys they expect to be written and
replace them with the next eligible keys of the order.

Faithfulness notes:
* `index` is not stored: `present` is read off the order.
* `split_order(order, removed, appended)` removes the rewritten keys' old
  pairs; as the order has one pair per key, that is filtering the written
  keys out of the order.
* `hint_writes`'s first loop is split into its three independent effects:
  recording hinted keys (with the new-key count), removing their marks, and
  collecting those marks (sorted) as retractions.
* `reconcile`'s side-effecting filter is modelled as in FIFO.
-/

set_option linter.unusedSectionVars false

namespace RightCash
namespace Lru

open Policies

variable {K : Type} [DecidableEq K]

/-- The Rust `LruWrite<K>` struct (the low watermark is a parameter of `policy`). -/
structure St (K : Type) where
  /-- Consensus: `(last-write height, key)`, oldest first. -/
  order : List (Nat × K)
  trigger : Option Nat
  marked : List K
  hintedKeys : List K
  hintedNewCount : Nat
  predictionSize : Option Nat
  nextCandidate : Nat

/-- The consensus part of `writes`: every written key moves to the back at
`height` (ties by key); on overflow, drain the oldest down to `low`. -/
def specWrites (le : K → K → Bool) (low : Nat) (order : List (Nat × K)) (ks : List K)
    (height cap : Nat) : List K × List (Nat × K) :=
  let written := sortDedup le ks
  let newCount := (written.filter (fun k => k ∉ keysOf order)).length
  let order1 := order.filter (fun e => e.2 ∉ written) ++ written.map (fun k => (height, k))
  evictPrefix le order1 (evictionCount low (order.length + newCount) cap)

/-- `LruWrite::reconcile`. -/
def reconcile (s : St K) (victims written : List K) : Prediction K × St K :=
  let m1 := s.marked.filter (fun k => k ∉ victims)
  (⟨victims.filter (fun k => k ∉ s.marked ∨ k ∈ written),
    if victims = [] then written.filter (fun k => k ∈ m1) else m1⟩,
   { s with marked := m1.filter (fun k => k ∉ written),
            predictionSize := if victims = [] then s.predictionSize else none,
            hintedKeys := [], hintedNewCount := 0, nextCandidate := 0 })

/-- `LruWrite::writes`. -/
def writes (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K) (height cap : Nat) :
    Eviction K × St K :=
  let r := specWrites le low s.order ks height cap
  let rc := reconcile { s with order := r.2 } r.1 (sortDedup le ks)
  (⟨r.1, rc.1.evict, rc.1.retract⟩, rc.2)

/-- `hint_writes`' candidate loop: walk the order from the cursor, marking
keys not hinted this block, until `count` keys are marked. Returns the new
marks, the marks and the cursor. -/
def fill (count : Nat) (hinted : List K) : List (Nat × K) → List K → Nat → List K × List K × Nat
  | [], m, cur => ([], m, cur)
  | (_, k) :: rest, m, cur =>
    if m.length < count then
      if k ∉ hinted ∧ k ∉ m then
        ((k :: (fill count hinted rest (m ++ [k]) (cur + 1)).1),
          (fill count hinted rest (m ++ [k]) (cur + 1)).2)
      else fill count hinted rest m (cur + 1)
    else ([], m, cur)

/-- `hint_writes`' first loop, recording part: add each key to `hinted_keys`,
counting distinct new keys absent from the set while `counting`. -/
def recordHints (present : K → Bool) (counting : Bool) : List K → List K → Nat → List K × Nat
  | [], h, n => (h, n)
  | k :: ks, h, n =>
    if k ∈ h then recordHints present counting ks h n
    else recordHints present counting ks (h ++ [k]) (if counting && !present k then n + 1 else n)

/-- `LruWrite::hint_writes`. -/
def hintWrites (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K) (cap margin : Nat) :
    Prediction K × St K :=
  let rh := recordHints (fun k => decide (k ∈ keysOf s.order)) s.predictionSize.isNone ks
    s.hintedKeys s.hintedNewCount
  let m1 := s.marked.filter (fun k => k ∉ ks)
  let predSize :=
    if s.predictionSize.isNone ∧ s.order.length + rh.2 ≥ s.trigger.getD cap
    then some ((cap - low) + margin) else s.predictionSize
  let fr := match predSize with
    | some count => fill count rh.1 (s.order.drop s.nextCandidate) m1 s.nextCandidate
    | none => ([], m1, s.nextCandidate)
  (⟨fr.1, (s.marked.filter (fun k => k ∈ ks)).mergeSort le⟩,
   { s with hintedKeys := rh.1, hintedNewCount := rh.2, marked := fr.2.1,
            predictionSize := predSize, nextCandidate := fr.2.2 })

/-- `LruWrite::reset_hints`. -/
def resetHints (s : St K) : St K :=
  { s with marked := [], hintedKeys := [], hintedNewCount := 0, predictionSize := none,
           nextCandidate := 0 }

/-- LRU-write with key comparison `le` and low watermark `low`, as a `Policy`. -/
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
  hintWrites := hintWrites le low
  resetHints := resetHints
  predicted := St.marked

/-! ## Proofs -/

theorem reconcile_order (s : St K) (v w : List K) : (reconcile s v w).2.order = s.order := rfl

theorem writes_order (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K) (h cap : Nat) :
    (writes le low s ks h cap).2.order = (specWrites le low s.order ks h cap).2 := rfl

theorem hintWrites_order (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K)
    (cap margin : Nat) : (hintWrites le low s ks cap margin).2.order = s.order := rfl

theorem mem_order1 (le : K → K → Bool) (order : List (Nat × K)) (ks : List K) (h : Nat) (k : K) :
    k ∈ keysOf (order.filter (fun e => e.2 ∉ sortDedup le ks) ++
        (sortDedup le ks).map (fun k => (h, k)))
      ↔ k ∈ keysOf order ∨ k ∈ ks := by
  rw [keysOf_append, keysOf_at, List.mem_append, mem_sortDedup]
  have : k ∈ keysOf (order.filter (fun e => e.2 ∉ sortDedup le ks)) ↔
      k ∈ keysOf order ∧ k ∉ ks := by
    simp only [mem_keysOf, List.mem_filter, decide_eq_true_eq, mem_sortDedup]
    constructor
    · rintro ⟨h, hm, hn⟩; exact ⟨⟨h, hm⟩, hn⟩
    · rintro ⟨⟨h, hm⟩, hn⟩; exact ⟨h, hm, hn⟩
  rw [this]
  by_cases hk : k ∈ ks <;> simp [hk]

theorem nodup_order1 (le : K → K → Bool) (order : List (Nat × K)) (ks : List K) (h : Nat)
    (hnd : (keysOf order).Nodup) :
    (keysOf (order.filter (fun e => e.2 ∉ sortDedup le ks) ++
      (sortDedup le ks).map (fun k => (h, k)))).Nodup := by
  rw [keysOf_append, keysOf_at, List.nodup_append]
  refine ⟨?_, nodup_sortDedup le ks, ?_⟩
  · exact hnd.sublist (List.Sublist.map _ List.filter_sublist)
  · intro a ha b hb hab
    subst hab
    simp only [mem_keysOf, List.mem_filter, decide_eq_true_eq] at ha
    obtain ⟨_, _, hn⟩ := ha
    exact hn hb

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

theorem reconcile_marked (s : St K) (v w : List K) (k : K)
    (hk : k ∈ (reconcile s v w).2.marked) : k ∈ s.marked ∧ k ∉ v ∧ k ∉ w := by
  simp only [reconcile, List.mem_filter, decide_eq_true_eq] at hk
  exact ⟨hk.1.1, hk.1.2, hk.2⟩

theorem marked_spec (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K) (h cap : Nat)
    (hwf : (keysOf s.order).Nodup) (hmt : ∀ k ∈ s.marked, k ∈ keysOf s.order) :
    ∀ k ∈ (writes le low s ks h cap).2.marked, k ∈ keysOf (writes le low s ks h cap).2.order := by
  intro k hk
  obtain ⟨hm, hv, _⟩ := reconcile_marked _ _ _ k hk
  rw [writes_order]
  exact (tracked_spec le low s.order ks h cap k hwf).2 ⟨Or.inl (hmt k hm), hv⟩

/-! ### Hint loops -/

theorem recordHints_mem (present : K → Bool) (counting : Bool) :
    ∀ (ks h : List K) (n : Nat) (k : K),
      k ∈ (recordHints present counting ks h n).1 ↔ k ∈ h ∨ k ∈ ks
  | [], h, n, k => by simp [recordHints]
  | k' :: ks, h, n, k => by
    unfold recordHints
    split
    · rename_i hk'
      rw [recordHints_mem present counting ks h n k]
      by_cases hk : k = k'
      · subst hk; simp [hk']
      · simp [hk]
    · rw [recordHints_mem present counting ks _ _ k]
      by_cases hk : k = k' <;> simp [hk]

theorem fill_spec (count : Nat) (hinted : List K) :
    ∀ (l : List (Nat × K)) (m : List K) (cur : Nat) (k : K),
      (k ∈ (fill count hinted l m cur).2.1 ↔ k ∈ m ∨ k ∈ (fill count hinted l m cur).1) ∧
      (k ∈ (fill count hinted l m cur).1 → k ∉ hinted ∧ k ∉ m ∧ k ∈ keysOf l)
  | [], m, cur, k => by simp [fill]
  | (h', k') :: rest, m, cur, k => by
    unfold fill
    split
    · split
      · rename_i hc
        obtain ⟨ih1, ih2⟩ := fill_spec count hinted rest (m ++ [k']) (cur + 1) k
        simp only [List.mem_cons]
        refine ⟨?_, ?_⟩
        · rw [ih1, List.mem_append, List.mem_singleton]
          constructor
          · rintro ((h | h) | h)
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          · rintro (h | h | h)
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
        · rintro (rfl | h)
          · exact ⟨hc.1, hc.2, by simp [keysOf]⟩
          · obtain ⟨a, b, c⟩ := ih2 h
            refine ⟨a, fun hm => b (List.mem_append_left _ hm), ?_⟩
            simp only [keysOf, List.map_cons, List.mem_cons] at c ⊢
            exact Or.inr c
      · obtain ⟨ih1, ih2⟩ := fill_spec count hinted rest m (cur + 1) k
        refine ⟨ih1, fun h => ?_⟩
        obtain ⟨a, b, c⟩ := ih2 h
        refine ⟨a, b, ?_⟩
        simp only [keysOf, List.map_cons, List.mem_cons] at c ⊢
        exact Or.inr c
    · simp

/-- The marks after a hint: the old marks minus the hinted keys, plus new ones. -/
theorem hint_parts (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K) (cap margin : Nat)
    (k : K) :
    (k ∈ (hintWrites le low s ks cap margin).2.marked ↔
      (k ∈ s.marked ∧ k ∉ ks) ∨ k ∈ (hintWrites le low s ks cap margin).1.evict) ∧
    (k ∈ (hintWrites le low s ks cap margin).1.evict → k ∉ ks ∧ k ∈ keysOf s.order) ∧
    (k ∈ (hintWrites le low s ks cap margin).1.retract ↔ k ∈ s.marked ∧ k ∈ ks) := by
  have hrec := recordHints_mem (fun k => decide (k ∈ keysOf s.order)) s.predictionSize.isNone ks
    s.hintedKeys s.hintedNewCount k
  refine ⟨?_, ?_, ?_⟩
  · unfold hintWrites
    simp only
    split
    · rw [(fill_spec _ _ _ _ _ k).1]
      simp only [List.mem_filter, decide_eq_true_eq]
    · simp only [List.mem_filter, decide_eq_true_eq, List.not_mem_nil, or_false]
  · unfold hintWrites
    simp only
    split
    · intro hk
      obtain ⟨hh, _, hko⟩ := (fill_spec _ _ _ _ _ k).2 hk
      refine ⟨fun hks => hh (hrec.2 (Or.inr hks)), ?_⟩
      rw [keysOf_drop] at hko
      exact List.mem_of_mem_drop hko
    · simp
  · simp [hintWrites, List.mem_mergeSort]

theorem hint_marked_spec (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K)
    (cap margin : Nat) (hm : ∀ k ∈ s.marked, k ∈ keysOf s.order) :
    ∀ k ∈ (hintWrites le low s ks cap margin).2.marked, k ∈ keysOf s.order := by
  intro k hk
  obtain ⟨h1, h2, _⟩ := hint_parts le low s ks cap margin k
  rcases h1.1 hk with h | h
  · exact hm k h.1
  · exact (h2 h).2

theorem hint_delta_spec (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K)
    (cap margin : Nat) :
    MarkDelta s.marked (hintWrites le low s ks cap margin).2.marked
      (hintWrites le low s ks cap margin).1.evict (hintWrites le low s ks cap margin).1.retract := by
  intro k
  obtain ⟨h1, h2, h3⟩ := hint_parts le low s ks cap margin k
  refine ⟨fun hR => ?_, fun _ hE => h1.2 (Or.inr hE), fun hR hE => ?_⟩
  · have hks := (h3.1 hR).2
    rw [h1]
    rintro (h | h)
    · exact h.2 hks
    · exact (h2 h).1 hks
  · rw [h1]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact absurd h hE
    · intro hm
      exact Or.inl ⟨hm, fun hks => hR (h3.2 ⟨hm, hks⟩)⟩

/-! ### Writes -/

theorem writes_kept (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K) (h cap : Nat)
    (hv : (specWrites le low s.order ks h cap).1 = []) :
    (writes le low s ks h cap).1.evict = [] ∧
    (writes le low s ks h cap).1.retract = (sortDedup le ks).filter (fun k => k ∈ s.marked) ∧
    (writes le low s ks h cap).2.marked = s.marked.filter (fun k => k ∉ sortDedup le ks) := by
  unfold writes reconcile
  simp only [hv]
  simp

theorem writes_final (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K) (h cap : Nat)
    (hv : (specWrites le low s.order ks h cap).1 ≠ []) :
    (writes le low s ks h cap).1.evict =
      (specWrites le low s.order ks h cap).1.filter
        (fun k => k ∉ s.marked ∨ k ∈ sortDedup le ks) ∧
    (writes le low s ks h cap).1.retract =
      s.marked.filter (fun k => k ∉ (specWrites le low s.order ks h cap).1) := by
  unfold writes reconcile
  simp only [hv]
  refine ⟨?_, ?_⟩ <;> first | trivial | rfl

theorem kept_spec (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K) (h cap : Nat)
    (hv : (specWrites le low s.order ks h cap).1 = []) :
    MarkDelta s.marked (writes le low s ks h cap).2.marked (writes le low s ks h cap).1.evict
        (writes le low s ks h cap).1.retract ∧
      ∀ k ∈ ks, k ∈ (writes le low s ks h cap).2.marked → k ∈ (writes le low s ks h cap).1.evict := by
  obtain ⟨he, hr, hm⟩ := writes_kept le low s ks h cap hv
  rw [he, hr, hm]
  refine ⟨fun k => ⟨fun hR => ?_, fun _ hE => absurd hE List.not_mem_nil, fun hR _ => ?_⟩,
    fun k hk hmk => ?_⟩
  · simp only [List.mem_filter, decide_eq_true_eq, mem_sortDedup] at hR ⊢
    exact fun h => h.2 hR.1
  · simp only [List.mem_filter, decide_eq_true_eq, mem_sortDedup] at hR ⊢
    constructor
    · exact fun h => h.1
    · intro hm; exact ⟨hm, fun hks => hR ⟨hks, hm⟩⟩
  · simp only [List.mem_filter, decide_eq_true_eq, mem_sortDedup] at hmk
    exact absurd hk hmk.2

theorem final_spec (le : K → K → Bool) (low : Nat) (s : St K) (ks : List K) (h cap : Nat)
    (hv : (specWrites le low s.order ks h cap).1 ≠ []) :
    FinalOK s.marked ks (writes le low s ks h cap).1 := by
  obtain ⟨he, hr⟩ := writes_final le low s ks h cap hv
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

/-- **LRU-write satisfies the policy laws.** -/
theorem lawful (le : K → K → Bool) (low : Nat) : (policy le low).Lawful where
  writes_victims _ _ _ _ := rfl
  writes_cons s ks h cap := writes_order le low s ks h cap
  hint_cons s ks cap margin := hintWrites_order le low s ks cap margin
  reset_cons _ := rfl
  reset_marked _ := rfl
  predicted_eq _ := rfl
  wf_fresh := List.nodup_nil
  fresh_tracked := rfl
  wf_writes c ks h cap hwf := wf_spec le low c ks h cap hwf
  tracked_writes c ks h cap k hwf := tracked_spec le low c ks h cap k hwf
  victims_sub c ks h cap k hk := victims_spec le low c ks h cap k hk
  writes_marked s ks h cap hwf hmt := marked_spec le low s ks h cap hwf hmt
  hint_marked s ks cap margin hm := hint_marked_spec le low s ks cap margin hm
  hint_delta s ks cap margin := hint_delta_spec le low s ks cap margin
  kept_delta s ks h cap hv := kept_spec le low s ks h cap hv
  final s ks h cap hv := final_spec le low s ks h cap hv

end Lru
end RightCash
