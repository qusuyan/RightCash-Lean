/-!
# Basic data model

Abstract counterparts of the plain data types in `src/types.rs` and
`src/set.rs` of RightCash.

* Keys `K` and values `V` are opaque. Rust keys are byte strings ordered
  lexicographically; the model needs only decidable equality, plus a key
  comparison `le` that the policies receive as a parameter (any comparison
  works, since only the *set* of keys matters to correctness).
* Finite maps are modelled as functions (`K → Option _`): equality of
  functions is extensional, which is exactly "same entries".
* `BatchOp` omits `PrefixDelete`: `RightCash::propose` rejects a batch
  containing one before touching any state (`Error::PrefixDeleteUnsupported`).
-/

namespace RightCash

/-- Pointwise update of a function (a finite-map `insert`). -/
def fupd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

@[simp] theorem fupd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    fupd f a b a = b := by simp [fupd]

theorem fupd_ne {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (b : β) (h : x ≠ a) :
    fupd f a b x = f x := by simp [fupd, h]

/-! ## Deduplication and sorting -/

/-- Remove duplicates (Rust: `sort_unstable` followed by `dedup` removes all
duplicates of a sorted vector). -/
def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: l => if a ∈ l then dedup l else a :: dedup l

@[simp] theorem mem_dedup {α : Type} [DecidableEq α] {a : α} :
    ∀ {l : List α}, a ∈ dedup l ↔ a ∈ l
  | [] => by simp [dedup]
  | b :: l => by
    by_cases h : b ∈ l
    · simp only [dedup, h, ite_true, mem_dedup, List.mem_cons]
      constructor
      · intro h'; exact Or.inr h'
      · rintro (rfl | h') <;> assumption
    · simp [dedup, h, mem_dedup]

theorem nodup_dedup {α : Type} [DecidableEq α] : ∀ (l : List α), (dedup l).Nodup
  | [] => List.nodup_nil
  | b :: l => by
    by_cases h : b ∈ l
    · simp only [dedup, h, ite_true]; exact nodup_dedup l
    · simp only [dedup, h, ite_false]
      exact List.nodup_cons.2 ⟨by simpa using h, nodup_dedup l⟩

/-- `written.sort_unstable(); written.dedup()` in the policies. -/
def sortDedup {K : Type} [DecidableEq K] (le : K → K → Bool) (l : List K) : List K :=
  dedup (l.mergeSort le)

@[simp] theorem mem_sortDedup {K : Type} [DecidableEq K] (le : K → K → Bool) {l : List K} {k : K} :
    k ∈ sortDedup le l ↔ k ∈ l := by
  simp [sortDedup, List.mem_mergeSort]

theorem nodup_sortDedup {K : Type} [DecidableEq K] (le : K → K → Bool) (l : List K) :
    (sortDedup le l).Nodup := nodup_dedup _

/-! ## Entries, batches and storage states -/

/-- A write-set entry (`set::Entry`): a value, or a tombstone left by a delete. -/
inductive Entry (V : Type) where
  | value (v : V)
  | tombstone
  deriving DecidableEq

/-- What an entry becomes in storage once evicted (`speculate::entry_op`):
a value is `Put`, a tombstone is a storage `Delete` (absence). -/
def Entry.toStore {V : Type} : Entry V → Option V
  | .value v => some v
  | .tombstone => none

/-- One operation of a batch (`types::BatchOp` without `PrefixDelete`). The
same type is used for write-set batches and storage batches. -/
inductive BatchOp (K V : Type) where
  | put (k : K) (v : V)
  | delete (k : K)

namespace BatchOp
variable {K V : Type}

def key : BatchOp K V → K
  | put k _ => k
  | delete k => k

/-- The op's effect on a storage state at its key. -/
def val : BatchOp K V → Option V
  | put _ v => some v
  | delete _ => none

/-- The op's effect on the write set at its key (a delete leaves a tombstone). -/
def entry : BatchOp K V → Entry V
  | put _ v => .value v
  | delete _ => .tombstone

/-- `speculate::entry_op`: the storage op that writes an entry. -/
def ofEntry (k : K) : Entry V → BatchOp K V
  | .value v => put k v
  | .tombstone => delete k

@[simp] theorem key_ofEntry (k : K) (e : Entry V) : (ofEntry k e).key = k := by
  cases e <;> rfl

@[simp] theorem val_ofEntry (k : K) (e : Entry V) : (ofEntry k e).val = e.toStore := by
  cases e <;> rfl

/-- The storage op that sets key `k` to `o` (`Put` if present, `Delete` if absent);
`speculate::put_back`. -/
def ofOption (k : K) : Option V → BatchOp K V
  | some v => put k v
  | none => delete k

@[simp] theorem key_ofOption (k : K) (o : Option V) : (ofOption k o).key = k := by
  cases o <;> rfl

@[simp] theorem val_ofOption (k : K) (o : Option V) : (ofOption k o).val = o := by
  cases o <;> rfl

end BatchOp

/-- A storage state: the key/value map a storage view exposes. The storage
engine is assumed correct, so a view *is* its state. -/
abbrev Store (K V : Type) := K → Option V

/-- A write set (a `Snapshot`'s records): key ↦ entry. -/
abbrev WriteSet (K V : Type) := K → Option (Entry V)

/-- The empty map. -/
def emptyMap {K β : Type} : K → Option β := fun _ => none

section Apply
variable {K V : Type} [DecidableEq K]

/-- Apply one storage op (correct storage engine: sequential application). -/
def applyOp (s : Store K V) (op : BatchOp K V) : Store K V := fupd s op.key op.val

/-- `StorageProposal::propose` on a correct engine: apply the batch in order. -/
def applyBatch (s : Store K V) (ops : List (BatchOp K V)) : Store K V := ops.foldl applyOp s

/-- `set::normalise`: the batch's final entry per key (the last op wins). -/
def batchFinal (b : List (BatchOp K V)) : WriteSet K V :=
  b.foldl (fun f op => fupd f op.key (some op.entry)) emptyMap

end Apply

theorem find?_eq_some_of_unique {α : Type} {p : α → Bool} {l : List α} {y : α}
    (huniq : ∀ x ∈ l, p x = true → x = y) (hy : y ∈ l) (hp : p y = true) :
    l.find? p = some y := by
  cases h : l.find? p with
  | none => exact absurd hp (List.find?_eq_none.1 h y hy)
  | some x => rw [huniq x (List.mem_of_find?_eq_some h) (List.find?_some h)]

/-! ## Last-writer-wins -/

/-- A fold of pointwise updates: at key `k` it holds the value of the *last*
update of `k`, or the initial value if there is none. -/
theorem foldl_fupd_apply {α ι β : Type} [DecidableEq ι] (key : α → ι) (val : α → β) :
    ∀ (l : List α) (f : ι → β) (k : ι),
      l.foldl (fun g a => fupd g (key a) (val a)) f k =
        (l.reverse.find? (fun a => decide (key a = k))).elim (f k) val
  | [], f, k => by simp
  | a :: l, f, k => by
    rw [List.foldl_cons, foldl_fupd_apply key val l, List.reverse_cons, List.find?_append]
    cases h : l.reverse.find? (fun a => decide (key a = k)) with
    | some b => simp
    | none =>
      by_cases hk : key a = k
      · subst hk; simp
      · have hk' : k ≠ key a := fun h => hk h.symm
        simp [hk, fupd_ne _ _ hk']

section ApplyLemmas
variable {K V : Type} [DecidableEq K]

theorem applyBatch_apply (s : Store K V) (ops : List (BatchOp K V)) (k : K) :
    applyBatch s ops k = (ops.reverse.find? (fun o => decide (o.key = k))).elim (s k) BatchOp.val :=
  foldl_fupd_apply BatchOp.key BatchOp.val ops s k

/-- If every op on a key writes the value `g key`, the batch result is `g k` on
the batch's keys and unchanged elsewhere; order and duplicates are immaterial. -/
theorem applyBatch_of_vals (s : Store K V) (ops : List (BatchOp K V)) (g : K → Option V)
    (hg : ∀ o ∈ ops, o.val = g o.key) (k : K) :
    applyBatch s ops k = if k ∈ ops.map BatchOp.key then g k else s k := by
  rw [applyBatch_apply]
  cases h : ops.reverse.find? (fun o => decide (o.key = k)) with
  | some o =>
    have hmem : o ∈ ops := List.mem_reverse.1 (List.mem_of_find?_eq_some h)
    have hkey : o.key = k := by simpa using List.find?_some h
    have : k ∈ ops.map BatchOp.key := List.mem_map.2 ⟨o, hmem, hkey⟩
    simp only [this, ite_true, Option.elim_some]
    rw [hg o hmem, hkey]
  | none =>
    have hno := List.find?_eq_none.1 h
    have : k ∉ ops.map BatchOp.key := by
      intro hk
      obtain ⟨o, ho, hok⟩ := List.mem_map.1 hk
      exact hno o (List.mem_reverse.2 ho) (by simpa using hok)
    simp [this]

theorem batchFinal_apply (b : List (BatchOp K V)) (k : K) :
    batchFinal b k = (b.reverse.find? (fun o => decide (o.key = k))).elim none (fun o => some o.entry) :=
  foldl_fupd_apply BatchOp.key (fun op => some op.entry) b emptyMap k

/-- The batch has a final entry exactly for the keys it writes. -/
theorem batchFinal_isSome (b : List (BatchOp K V)) (k : K) :
    (batchFinal b k).isSome ↔ k ∈ b.map BatchOp.key := by
  rw [batchFinal_apply]
  cases h : b.reverse.find? (fun o => decide (o.key = k)) with
  | some o =>
    simp only [Option.elim_some, Option.isSome_some, true_iff]
    exact List.mem_map.2 ⟨o, List.mem_reverse.1 (List.mem_of_find?_eq_some h),
      by simpa using List.find?_some h⟩
  | none =>
    simp only [Option.elim_none, Option.isSome_none, Bool.false_eq_true, false_iff]
    intro hk
    obtain ⟨o, ho, hok⟩ := List.mem_map.1 hk
    exact List.find?_eq_none.1 h o (List.mem_reverse.2 ho) (by simpa using hok)

theorem batchFinal_eq_none (b : List (BatchOp K V)) (k : K) :
    batchFinal b k = none ↔ k ∉ b.map BatchOp.key := by
  rw [← batchFinal_isSome]; cases batchFinal b k <;> simp

end ApplyLemmas

end RightCash
