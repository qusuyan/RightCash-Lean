import RightCash.Basic

/-!
# Sorted record lists

The Rust snapshot keeps its records in a `Vec` sorted by key (`set.rs`), and
the commitment schemes see entries "in ascending distinct-key order". This
file gives the key order (`KeyOrder`, the `Ord` on key bytes), sorted lists of
`(key, payload)` records, and their meaning as finite maps (`toMap`).
-/

set_option linter.unusedSectionVars false

namespace RightCash

/-- A strict total order on keys (Rust: `Ord` on the key bytes). -/
structure KeyOrder (K : Type) where
  lt : K → K → Bool
  irrefl : ∀ a, lt a a = false
  trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true
  total : ∀ a b, a ≠ b → lt a b = true ∨ lt b a = true

namespace KeyOrder
variable {K : Type} (o : KeyOrder K)

theorem ne_of_lt {a b : K} (h : o.lt a b = true) : a ≠ b := by
  rintro rfl; rw [o.irrefl] at h; cases h

theorem not_lt_of_lt {a b : K} (h : o.lt a b = true) : o.lt b a = false := by
  cases h' : o.lt b a
  · rfl
  · have := o.trans _ _ _ h h'; rw [o.irrefl] at this; cases this

end KeyOrder

section Sorted
variable {K α : Type} [DecidableEq K] (o : KeyOrder K)

/-- Strictly increasing keys. -/
def Sorted (L : List (K × α)) : Prop := L.Pairwise (fun a b => o.lt a.1 b.1 = true)

/-- The finite map a record list stands for (the first record of a key wins;
sorted lists have one record per key). -/
def toMap : List (K × α) → K → Option α
  | [], _ => none
  | (k, a) :: L, k' => if k' = k then some a else toMap L k'

def keysL (L : List (K × α)) : List K := L.map Prod.fst

@[simp] theorem toMap_nil (k : K) : toMap ([] : List (K × α)) k = none := rfl

theorem toMap_cons (k : K) (a : α) (L : List (K × α)) (k' : K) :
    toMap ((k, a) :: L) k' = if k' = k then some a else toMap L k' := rfl

@[simp] theorem keysL_nil : keysL ([] : List (K × α)) = [] := rfl

@[simp] theorem keysL_cons (x : K × α) (L : List (K × α)) : keysL (x :: L) = x.1 :: keysL L := rfl

theorem toMap_isSome (L : List (K × α)) (k : K) : (toMap L k).isSome ↔ k ∈ keysL L := by
  induction L with
  | nil => simp
  | cons x L ih =>
    obtain ⟨k', a⟩ := x
    rw [toMap_cons]
    by_cases h : k = k' <;> simp [h, ih]

theorem toMap_eq_none (L : List (K × α)) (k : K) : toMap L k = none ↔ k ∉ keysL L := by
  rw [← toMap_isSome]; cases toMap L k <;> simp

theorem mem_keysL_of_toMap {L : List (K × α)} {k : K} {a : α} (h : toMap L k = some a) :
    k ∈ keysL L := (toMap_isSome L k).1 (by rw [h]; rfl)

theorem sorted_cons {x : K × α} {L : List (K × α)} :
    Sorted o (x :: L) ↔ (∀ y ∈ L, o.lt x.1 y.1 = true) ∧ Sorted o L := List.pairwise_cons

theorem lt_of_sorted_cons {x : K × α} {L : List (K × α)} (h : Sorted o (x :: L)) {k : K}
    (hk : k ∈ keysL L) : o.lt x.1 k = true := by
  simp only [keysL, List.mem_map] at hk
  obtain ⟨y, hy, rfl⟩ := hk
  exact (sorted_cons o).1 h |>.1 y hy

theorem not_mem_tail_of_sorted {k : K} {a : α} {L : List (K × α)} (h : Sorted o ((k, a) :: L)) :
    k ∉ keysL L := fun hk => o.ne_of_lt (lt_of_sorted_cons o h hk) rfl

/-- In a sorted list, every key below the head is absent. -/
theorem toMap_below_head {k : K} {a : α} {L : List (K × α)} (h : Sorted o ((k, a) :: L)) {k' : K}
    (hk : o.lt k' k = true) : toMap ((k, a) :: L) k' = none := by
  rw [toMap_eq_none]
  intro hm
  simp only [keysL_cons, List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact o.ne_of_lt hk rfl
  · have := o.trans _ _ _ hk (lt_of_sorted_cons o h hm)
    rw [o.irrefl] at this; cases this

/-- **A sorted list is determined by the map it stands for.** -/
theorem sorted_ext : ∀ {L L' : List (K × α)}, Sorted o L → Sorted o L' →
    (∀ k, toMap L k = toMap L' k) → L = L'
  | [], [], _, _, _ => rfl
  | [], (k, a) :: _, _, _, h => by have := h k; simp [toMap_cons] at this
  | (k, a) :: _, [], _, _, h => by have := h k; simp [toMap_cons] at this
  | (k, a) :: L, (k', a') :: L', hs, hs', h => by
    have hk : k = k' := by
      by_cases hne : k = k'
      · exact hne
      exfalso
      rcases o.total k k' hne with hlt | hlt
      · have := h k
        rw [toMap_below_head o hs' hlt, toMap_cons, ite_eq_left rfl] at this; cases this
      · have := h k'
        rw [toMap_below_head o hs hlt, toMap_cons, ite_eq_left rfl] at this; cases this
    subst hk
    have ha : a = a' := by
      have := h k; simpa [toMap_cons] using this
    subst ha
    have : L = L' := sorted_ext ((sorted_cons o).1 hs).2 ((sorted_cons o).1 hs').2 (fun k' => by
      by_cases hk' : k' = k
      · subst hk'
        rw [(toMap_eq_none L k').2 (not_mem_tail_of_sorted o hs),
          (toMap_eq_none L' k').2 (not_mem_tail_of_sorted o hs')]
      · have := h k'; simpa [toMap_cons, hk'] using this)
    rw [this]

end Sorted

end RightCash
