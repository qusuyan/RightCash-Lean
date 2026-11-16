import RightCash.Impl.Merge

/-!
# The value arena (`set::Arena`, `ValueRef`, `Slot`, `normalise`, `compact`)

A snapshot's records hold `Slot`s: a tombstone, or `(chunk, offset, len)` into
its arena's chunk list. Chunks are immutable byte arrays shared by `Arc`
between snapshots. A child's arena is a copy of the parent's chunk list with
at most one new chunk appended (the batch's put values, `normalise`), or,
after `compact`, a single fresh chunk holding exactly its retained values.

Proved here:
* `pack_read`: every slot `normalise` creates reads back its op's value;
* `read_append`: a parent's slots read the same bytes in the child's arena;
* `compact_decode`, `compact_wf`: compaction preserves every record's entry
  and leaves every slot in bounds of the new chunk;
* `referenced_not_freed`: in a well-formed snapshot, the chunk behind every
  value slot is one of the snapshot's own chunks, in bounds. With `Arc`
  ownership (a chunk is freed only when no arena holds it) it is therefore
  never freed while any revision referencing it is alive.

Rust's `u32` offsets (`offset_u32` panics beyond 4 GiB) are modelled as
`Nat`; `live`/`total` only decide *when* to compact, not what a slot reads,
so they are omitted.
-/

set_option linter.unusedSectionVars false

namespace RightCash

abbrev Bytes := List UInt8

/-- An immutable chunk (`Arc<[u8]>`); `id` is its allocation identity. -/
structure Chunk where
  id : Nat
  bytes : Bytes

/-- `set::Slot` with its `ValueRef`. -/
inductive Slot where
  | value (chunk off len : Nat)
  | tombstone

/-- `set::Arena`: the chunk pointers a snapshot owns. -/
structure Arena where
  chunks : List Chunk

namespace Arena

/-- `Arena::entry`: resolve a slot (`none` where Rust's slicing would panic). -/
def read (A : Arena) : Slot → Option (Entry Bytes)
  | .value c off len =>
    match A.chunks[c]? with
    | some ch => if off + len ≤ ch.bytes.length then some (.value ((ch.bytes.drop off).take len)) else none
    | none => none
  | .tombstone => some .tombstone

/-- Every record's slot resolves inside this arena. -/
def WF {K : Type} (A : Arena) (recs : List (K × Slot)) : Prop := ∀ x ∈ recs, A.read x.2 ≠ none

/-- The entries a record list stands for. -/
def decode {K : Type} (A : Arena) (recs : List (K × Slot)) : List (K × Entry Bytes) :=
  recs.map (fun x => (x.1, (A.read x.2).getD .tombstone))

/-- Appending chunks (the child's copy plus its new chunk) never changes what
an in-bounds slot reads. -/
theorem read_append (A : Arena) (more : List Chunk) (s : Slot) (h : A.read s ≠ none) :
    (⟨A.chunks ++ more⟩ : Arena).read s = A.read s := by
  cases s with
  | tombstone => rfl
  | value c off len =>
    simp only [read] at h ⊢
    cases hc : A.chunks[c]? with
    | none => rw [hc] at h; exact absurd rfl h
    | some ch =>
      have hlt : c < A.chunks.length := by
        cases Nat.lt_or_ge c A.chunks.length with
        | inl h' => exact h'
        | inr h' => rw [List.getElem?_eq_none h'] at hc; cases hc
      rw [List.getElem?_append_left hlt, hc]

/-! ## `normalise`: packing a batch's values into one chunk -/

/-- One slot per op, in batch order, and the chunk bytes: every put value
appended at a running offset (superseded values included, as in Rust). -/
def packBatch {K : Type} (ci : Nat) : List (BatchOp K Bytes) → Nat → Bytes × List (K × Slot)
  | [], _ => ([], [])
  | .put k v :: rest, off =>
    ((v ++ (packBatch ci rest (off + v.length)).1), (k, .value ci off v.length) :: (packBatch ci rest (off + v.length)).2)
  | .delete k :: rest, off => ((packBatch ci rest off).1, (k, .tombstone) :: (packBatch ci rest off).2)

/-- Every packed slot reads back its op's entry from any arena whose chunk
`ci` contains the packed bytes at the right offset. -/
theorem pack_read {K : Type} (ci : Nat) (A : Arena) (ch : Chunk) (hA : A.chunks[ci]? = some ch) :
    ∀ (b : List (BatchOp K Bytes)) (off : Nat) (T : Bytes), off ≤ ch.bytes.length →
      ch.bytes.drop off = (packBatch ci b off).1 ++ T →
      (packBatch ci b off).2.map (fun x => (x.1, A.read x.2)) = b.map (fun op => (op.key, some op.entry))
  | [], _, _, _, _ => rfl
  | .put k v :: rest, off, T, hoff, h => by
    simp only [packBatch, List.map_cons] at h ⊢
    have hlen : off + v.length ≤ ch.bytes.length := by
      have := congrArg List.length h
      simp only [List.length_drop, List.length_append] at this
      omega
    have htake : (ch.bytes.drop off).take v.length = v := by rw [h, List.append_assoc]; simp
    have hrest : ch.bytes.drop (off + v.length) = (packBatch ci rest (off + v.length)).1 ++ T := by
      rw [← List.drop_drop, h, List.append_assoc]; simp
    rw [pack_read ci A ch hA rest (off + v.length) T hlen hrest]
    simp [read, hA, hlen, htake, BatchOp.key, BatchOp.entry]
  | .delete k :: rest, off, T, hoff, h => by
    simp only [packBatch, List.map_cons] at h ⊢
    rw [pack_read ci A ch hA rest off T hoff h]
    rfl

/-! ## `normalise`: stable sort by key, last op wins -/

/-- Insert into a sorted list, replacing an existing record of the key. The
fold of it over the packed ops is `ops.sort_by(key)` (stable) followed by the
dedup that keeps the last op's slot. -/
def supsert {K α : Type} [DecidableEq K] (o : KeyOrder K) : List (K × α) → K × α → List (K × α)
  | [], x => [x]
  | (k, a) :: L, (k', a') =>
    if k' = k then (k', a') :: L
    else if o.lt k' k then (k', a') :: (k, a) :: L
    else (k, a) :: supsert o L (k', a')

section Supsert
variable {K α : Type} [DecidableEq K] (o : KeyOrder K)

theorem toMap_supsert : ∀ (L : List (K × α)) (x : K × α) (k : K),
    toMap (supsert o L x) k = if k = x.1 then some x.2 else toMap L k
  | [], ⟨k', a'⟩, k => by simp [supsert, toMap_cons]
  | (k0, a) :: L, ⟨k', a'⟩, k => by
    unfold supsert
    by_cases h1 : k' = k0
    · subst h1; simp only [ite_true, toMap_cons]; by_cases hk : k = k' <;> simp [hk]
    · rw [ite_eq_right h1]
      by_cases h2 : o.lt k' k0 = true
      · rw [ite_eq_left h2]; simp only [toMap_cons]
      · rw [ite_eq_right h2, toMap_cons, toMap_supsert L ⟨k', a'⟩ k, toMap_cons]
        by_cases hk : k = k0
        · subst hk; simp [Ne.symm h1]
        · simp [hk]

theorem sorted_supsert : ∀ (L : List (K × α)) (x : K × α), Sorted o L → Sorted o (supsert o L x)
  | [], x, _ => List.pairwise_singleton _ _
  | (k0, a) :: L, ⟨k', a'⟩, hs => by
    unfold supsert
    have hsc := (sorted_cons o).1 hs
    by_cases h1 : k' = k0
    · subst h1; rw [ite_eq_left rfl]; exact (sorted_cons o).2 ⟨fun y hy => hsc.1 y hy, hsc.2⟩
    · rw [ite_eq_right h1]
      by_cases h2 : o.lt k' k0 = true
      · rw [ite_eq_left h2]
        refine (sorted_cons o).2 ⟨fun y hy => ?_, hs⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact h2
        · exact o.trans _ _ _ h2 (hsc.1 y hy)
      · rw [ite_eq_right h2]
        have hgt : o.lt k0 k' = true := by
          rcases o.total k' k0 h1 with h | h
          · exact absurd h h2
          · exact h
        refine (sorted_cons o).2 ⟨fun y hy => ?_, sorted_supsert L ⟨k', a'⟩ hsc.2⟩
        have hy' : (toMap (supsert o L ⟨k', a'⟩) y.1).isSome :=
          (toMap_isSome _ _).2 (List.mem_map.2 ⟨y, hy, rfl⟩)
        rw [toMap_supsert] at hy'
        by_cases hk : y.1 = k'
        · rw [hk]; exact hgt
        · rw [ite_eq_right hk, toMap_isSome] at hy'
          exact lt_of_sorted_cons o hs hy'

theorem supsert_map {β : Type} (f : α → β) : ∀ (L : List (K × α)) (x : K × α),
    (supsert o L x).map (fun y => (y.1, f y.2)) = supsert o (L.map (fun y => (y.1, f y.2))) (x.1, f x.2)
  | [], _ => rfl
  | (k0, a) :: L, ⟨k', a'⟩ => by
    unfold supsert
    by_cases h1 : k' = k0
    · simp [h1]
    · by_cases h2 : o.lt k' k0 = true
      · simp [h1, h2]
      · simp only [h1, h2, ite_false, Bool.false_eq_true, List.map_cons]
        rw [supsert_map f L ⟨k', a'⟩]

/-- The normalised ops: fold `supsert` over the packed ops. -/
def normOps (packed : List (K × α)) : List (K × α) := packed.foldl (supsert o) []

theorem sorted_normOps (packed : List (K × α)) : Sorted o (normOps o packed) := by
  unfold normOps
  suffices ∀ (L : List (K × α)), Sorted o L → Sorted o (packed.foldl (supsert o) L) from
    this [] List.Pairwise.nil
  induction packed with
  | nil => intro L h; exact h
  | cons x xs ih => intro L h; exact ih _ (sorted_supsert o L x h)

theorem toMap_normOps (packed : List (K × α)) (k : K) :
    toMap (normOps o packed) k = (packed.reverse.find? (fun x => decide (x.1 = k))).map Prod.snd := by
  unfold normOps
  suffices ∀ (L : List (K × α)), toMap (packed.foldl (supsert o) L) k =
      ((packed.reverse.find? (fun x => decide (x.1 = k))).map Prod.snd).or (toMap L k) by
    rw [this]; cases (packed.reverse.find? (fun x => decide (x.1 = k))).map Prod.snd <;> rfl
  induction packed with
  | nil => intro L; simp
  | cons x xs ih =>
    intro L
    rw [List.foldl_cons, ih, toMap_supsert, List.reverse_cons, List.find?_append]
    cases xs.reverse.find? (fun x => decide (x.1 = k)) with
    | some y => simp
    | none =>
      by_cases hk : k = x.1
      · subst hk; simp
      · have : x.1 ≠ k := fun h => hk h.symm
        simp [hk, this]

theorem normOps_map {β : Type} (f : α → β) (packed : List (K × α)) :
    (normOps o packed).map (fun y => (y.1, f y.2)) = normOps o (packed.map (fun y => (y.1, f y.2))) := by
  unfold normOps
  suffices ∀ L : List (K × α), (packed.foldl (supsert o) L).map (fun y => (y.1, f y.2)) =
      (packed.map (fun y => (y.1, f y.2))).foldl (supsert o) (L.map (fun y => (y.1, f y.2))) from this []
  induction packed with
  | nil => intro L; rfl
  | cons x xs ih => intro L; simp only [List.foldl_cons, List.map_cons]; rw [ih, supsert_map]

end Supsert

/-! ## `compact` -/

/-- Copy every retained value into one new chunk, in record order. -/
def compactAux {K : Type} (A : Arena) : List (K × Slot) → Nat → Bytes × List (K × Slot)
  | [], _ => ([], [])
  | (k, s) :: rest, off =>
    match A.read s with
    | some (.value bytes) =>
      (bytes ++ (compactAux A rest (off + bytes.length)).1,
        (k, .value 0 off bytes.length) :: (compactAux A rest (off + bytes.length)).2)
    | _ => ((compactAux A rest off).1, (k, .tombstone) :: (compactAux A rest off).2)

/-- `Arena::compact`: the new arena holds only the fresh chunk `id`. -/
def compact {K : Type} (A : Arena) (recs : List (K × Slot)) (id : Nat) : Arena × List (K × Slot) :=
  (⟨[⟨id, (compactAux A recs 0).1⟩]⟩, (compactAux A recs 0).2)

theorem compactAux_read {K : Type} (A : Arena) (ch : Chunk) :
    ∀ (recs : List (K × Slot)) (off : Nat) (T : Bytes), WF A recs → off ≤ ch.bytes.length →
      ch.bytes.drop off = (compactAux A recs off).1 ++ T →
      (compactAux A recs off).2.map (fun x => (x.1, (⟨[ch]⟩ : Arena).read x.2)) =
        recs.map (fun x => (x.1, A.read x.2))
  | [], _, _, _, _, _ => rfl
  | (k, s) :: rest, off, T, hwf, hoff, h => by
    have hwf' : WF A rest := fun x hx => hwf x (List.mem_cons_of_mem _ hx)
    have hs : A.read s ≠ none := hwf (k, s) (List.mem_cons_self ..)
    unfold compactAux at h ⊢
    cases hr : A.read s with
    | none => exact absurd hr hs
    | some e =>
      cases e with
      | tombstone =>
        simp only [hr] at h ⊢
        rw [List.map_cons, List.map_cons, compactAux_read A ch rest off T hwf' hoff h]
        simp only [hr]
        rfl
      | value bytes =>
        simp only [hr] at h ⊢
        have hlen : off + bytes.length ≤ ch.bytes.length := by
          have := congrArg List.length h
          simp only [List.length_drop, List.length_append] at this
          omega
        have htake : (ch.bytes.drop off).take bytes.length = bytes := by
          rw [h, List.append_assoc]; simp
        have hrest : ch.bytes.drop (off + bytes.length) = (compactAux A rest (off + bytes.length)).1 ++ T := by
          rw [← List.drop_drop, h, List.append_assoc]; simp
        rw [List.map_cons, List.map_cons, compactAux_read A ch rest (off + bytes.length) T hwf' hlen hrest]
        simp only [hr]
        simp [read, hlen, htake]

/-- **Compaction preserves every record's entry.** -/
theorem compact_decode {K : Type} (A : Arena) (recs : List (K × Slot)) (id : Nat) (hwf : WF A recs) :
    (compact A recs id).2.map (fun x => (x.1, (compact A recs id).1.read x.2)) =
      recs.map (fun x => (x.1, A.read x.2)) :=
  compactAux_read A ⟨id, (compactAux A recs 0).1⟩ recs 0 [] hwf (Nat.zero_le _) (by simp)

/-- **Compaction leaves every slot in bounds of the new chunk.** -/
theorem compact_wf {K : Type} (A : Arena) (recs : List (K × Slot)) (id : Nat) (hwf : WF A recs) :
    WF (compact A recs id).1 (compact A recs id).2 := by
  intro x hx
  have h := compact_decode A recs id hwf
  have hm : (x.1, (compact A recs id).1.read x.2) ∈ recs.map (fun x => (x.1, A.read x.2)) := by
    rw [← h]; exact List.mem_map.2 ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := List.mem_map.1 hm
  have : (compact A recs id).1.read x.2 = A.read y.2 := (Prod.mk.inj hxy).2.symm
  rw [this]; exact hwf y hy

/-! ## Nothing referenced is ever freed -/

/-- With `Arc` chunks, a chunk is freed once no live arena holds it. -/
def Freed (live : List Arena) (id : Nat) : Prop := ∀ A ∈ live, ∀ ch ∈ A.chunks, ch.id ≠ id

/-- **No use after free.** In a well-formed live snapshot, every value slot
points into one of the snapshot's own chunks, within its bounds, so that
chunk is not freed while the snapshot is alive. -/
theorem referenced_not_freed {K : Type} (live : List Arena) (A : Arena) (hA : A ∈ live)
    (recs : List (K × Slot)) (hwf : WF A recs) (x : K × Slot) (hx : x ∈ recs)
    (c off len : Nat) (hs : x.2 = .value c off len) :
    ∃ ch, A.chunks[c]? = some ch ∧ off + len ≤ ch.bytes.length ∧ ¬ Freed live ch.id := by
  have h := hwf x hx
  rw [hs] at h
  simp only [read] at h
  cases hc : A.chunks[c]? with
  | none => rw [hc] at h; exact absurd rfl h
  | some ch =>
    rw [hc] at h
    have hb : off + len ≤ ch.bytes.length := by
      by_cases hb : off + len ≤ ch.bytes.length
      · exact hb
      · simp [hb] at h
    refine ⟨ch, rfl, hb, fun hf => hf A hA ch (List.mem_of_getElem? hc) rfl⟩

end Arena

end RightCash
