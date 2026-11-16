import RightCash.Policy

/-!
# Shared pieces of the v0 policies (`src/policy/mod.rs`)

Both FIFO and LRU-write keep their consensus state as an *eviction order*:
a list of `(height, key)` pairs, oldest first, one per tracked key. (The
Rust `index` is a key-sorted copy of the same pairs, kept for binary search;
the model derives it from the order.) A batch appends keys at the new
height, and an eviction drains a prefix of the order.
-/

set_option linter.unusedSectionVars false

namespace RightCash
namespace Policies

variable {K : Type} [DecidableEq K]

/-- The tracked keys of an order. -/
def keysOf (order : List (Nat × K)) : List K := order.map Prod.snd

/-- `eviction_count`: nothing within capacity; otherwise down to the low
watermark. -/
def evictionCount (low len cap : Nat) : Nat := if len > cap then len - low else 0

/-- Drain the first `cnt` entries of `order` (`order.drain(..cnt.min(len))`):
the victims, sorted by key (`all_evicted_keys.sort_unstable()`), and the rest. -/
def evictPrefix (le : K → K → Bool) (order : List (Nat × K)) (cnt : Nat) :
    List K × List (Nat × K) :=
  ((keysOf (order.take cnt)).mergeSort le, order.drop cnt)

/-- `params_digest` input and `validate_watermarks` are not needed by the proofs. -/

theorem mem_drop_iff_of_nodup {α : Type} {L : List α} (n : Nat) (hL : L.Nodup) {a : α} :
    a ∈ L.drop n ↔ a ∈ L ∧ a ∉ L.take n := by
  have hsplit := List.take_append_drop n L
  rw [← hsplit] at hL
  obtain ⟨_, _, hdisj⟩ := List.nodup_append.1 hL
  constructor
  · intro ha
    exact ⟨List.mem_of_mem_drop ha, fun ht => hdisj a ht a ha rfl⟩
  · rintro ⟨ha, hnt⟩
    rw [← hsplit, List.mem_append] at ha
    rcases ha with h | h
    · exact absurd h hnt
    · exact h

theorem keysOf_take (order : List (Nat × K)) (n : Nat) :
    keysOf (order.take n) = (keysOf order).take n := by
  simp [keysOf, List.map_take]

theorem keysOf_drop (order : List (Nat × K)) (n : Nat) :
    keysOf (order.drop n) = (keysOf order).drop n := by
  simp [keysOf, List.map_drop]

theorem mem_keysOf {order : List (Nat × K)} {k : K} :
    k ∈ keysOf order ↔ ∃ h, (h, k) ∈ order := by
  simp only [keysOf, List.mem_map]
  constructor
  · rintro ⟨⟨h, k'⟩, hm, rfl⟩; exact ⟨h, hm⟩
  · rintro ⟨h, hm⟩; exact ⟨(h, k), hm, rfl⟩

theorem keysOf_append (o₁ o₂ : List (Nat × K)) : keysOf (o₁ ++ o₂) = keysOf o₁ ++ keysOf o₂ := by
  simp [keysOf]

theorem keysOf_at (h : Nat) (ks : List K) : keysOf (ks.map (fun k => (h, k))) = ks := by
  simp [keysOf, Function.comp_def]

theorem mem_evictPrefix_victims (le : K → K → Bool) (order : List (Nat × K)) (cnt : Nat) {k : K} :
    k ∈ (evictPrefix le order cnt).1 ↔ k ∈ (keysOf order).take cnt := by
  simp [evictPrefix, List.mem_mergeSort, keysOf_take]

/-- After draining a prefix of an order with distinct keys, a key is tracked
iff it was tracked and is not a victim. -/
theorem mem_evictPrefix_rest (le : K → K → Bool) (order : List (Nat × K)) (cnt : Nat)
    (hnd : (keysOf order).Nodup) {k : K} :
    k ∈ keysOf (evictPrefix le order cnt).2 ↔ k ∈ keysOf order ∧ k ∉ (evictPrefix le order cnt).1 := by
  rw [mem_evictPrefix_victims, evictPrefix, keysOf_drop]
  exact mem_drop_iff_of_nodup cnt hnd

theorem nodup_evictPrefix_rest (le : K → K → Bool) (order : List (Nat × K)) (cnt : Nat)
    (hnd : (keysOf order).Nodup) : (keysOf (evictPrefix le order cnt).2).Nodup := by
  rw [evictPrefix, keysOf_drop]
  exact hnd.sublist (List.drop_sublist _ _)

theorem victims_mem_order (le : K → K → Bool) (order : List (Nat × K)) (cnt : Nat) {k : K}
    (hk : k ∈ (evictPrefix le order cnt).1) : k ∈ keysOf order :=
  List.mem_of_mem_take ((mem_evictPrefix_victims le order cnt).1 hk)

/-! ## Inserting new marks -/

/-- `for key in candidates { if marked.insert(key) { evict.push(key) } }`:
the newly marked keys and the new marks. -/
def insertNew : List K → List K → List K × List K
  | [], m => ([], m)
  | k :: ks, m =>
    if k ∈ m then insertNew ks m
    else ((k :: (insertNew ks (m ++ [k])).1), (insertNew ks (m ++ [k])).2)

theorem insertNew_spec : ∀ (c m : List K) (k : K),
    (k ∈ (insertNew c m).2 ↔ k ∈ m ∨ k ∈ c) ∧ (k ∈ (insertNew c m).1 ↔ k ∈ c ∧ k ∉ m)
  | [], m, k => by simp [insertNew]
  | k' :: c, m, k => by
    by_cases hk' : k' ∈ m
    · simp only [insertNew, hk', ite_true]
      obtain ⟨h1, h2⟩ := insertNew_spec c m k
      rw [h1, h2]
      by_cases hk : k = k'
      · subst hk; simp [hk']
      · simp [hk]
    · simp only [insertNew, hk', ite_false]
      obtain ⟨h1, h2⟩ := insertNew_spec c (m ++ [k']) k
      rw [h1]
      simp only [List.mem_cons, h2]
      by_cases hk : k = k'
      · subst hk; simp [hk']
      · simp [hk]

/-- `BTreeSet::insert` on a list-backed set. -/
def setInsert (l : List K) (k : K) : List K := if k ∈ l then l else l ++ [k]

end Policies
end RightCash
