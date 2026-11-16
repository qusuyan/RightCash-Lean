import RightCash.Impl.Arena
import RightCash.Impl.VC
import RightCash.Engine

/-!
# The concrete snapshot (`set::Snapshot::apply`)

A concrete snapshot is what the Rust `Snapshot` stores for consensus: sorted
records with arena slots, the arena, the commitment scheme instance and the
stored commitment digest. `Snap.apply` follows `Snapshot::apply`:
`normalise` (pack the batch into a new chunk; stable-sort by key, last op
wins), `merge` (reporting each change to the scheme), optional `compact`,
then `commitment`.

`snap_apply` proves that if the parent is well formed, so is the child, and:
* the child's entries are the abstract child write set (`childWS`, the map
  the engine model uses), and the evicted entries are the engine model's
  final entries of the victims, in victim order;
* every record's slot reads inside the child's own arena (`Arena.WF`), so by
  `Arena.referenced_not_freed` no referenced chunk is ever freed;
* the stored digest is `F` of the child's sorted entries, for every correct
  scheme (`VCImpl.Correct`: `rehash`, `lthash`, `SMT.scheme`, `MB3.scheme`).

Compaction is a free choice (`compactNow`), since `wants_compaction` only
affects memory use. Values are byte strings (`Bytes`).
-/

set_option linter.unusedSectionVars false

namespace RightCash

section Helpers
variable {K α β : Type} [DecidableEq K] (o : KeyOrder K)

def mapP (f : α → β) (L : List (K × α)) : List (K × β) := L.map (fun x => (x.1, f x.2))

@[simp] theorem keysL_mapP (f : α → β) (L : List (K × α)) : keysL (mapP f L) = keysL L := by
  simp [mapP, keysL, Function.comp_def]

theorem toMap_mapP (f : α → β) (L : List (K × α)) (k : K) : toMap (mapP f L) k = (toMap L k).map f := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    obtain ⟨k', a⟩ := x
    simp only [mapP, List.map_cons] at ih ⊢
    rw [toMap_cons, toMap_cons]
    by_cases hk : k = k' <;> simp [hk, ih]

theorem sorted_mapP (f : α → β) (L : List (K × α)) : Sorted o (mapP f L) ↔ Sorted o L := by
  simp [Sorted, mapP, List.pairwise_map]

theorem toMap_of_mem {L : List (K × α)} (hs : Sorted o L) {x : K × α} (hx : x ∈ L) :
    toMap L x.1 = some x.2 := by
  induction L with
  | nil => cases hx
  | cons y L ih =>
    obtain ⟨k, a⟩ := y
    rw [toMap_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · simp
    · have hne : x.1 ≠ k := fun h => not_mem_tail_of_sorted o hs (h ▸ List.mem_map.2 ⟨x, hx, rfl⟩)
      rw [ite_eq_right hne]; exact ih ((sorted_cons o).1 hs).2 hx

/-- Every record `merge` keeps carries a payload taken from its inputs. -/
theorem merge_entries_pred (Q : α → Bool) (p q : List (K × α)) (vs : List K) (hpre : MPre o p q vs)
    (hp : ∀ x ∈ p, Q x.2 = true) (hq : ∀ x ∈ q, Q x.2 = true) :
    ∀ x ∈ (merge o p q vs).entries, Q x.2 = true := by
  intro x hx
  have hpre' : MPre o (mapP Q p) (mapP Q q) vs :=
    ⟨(sorted_mapP o Q p).2 hpre.1, (sorted_mapP o Q q).2 hpre.2.1, hpre.2.2.1,
      fun v hv => by simpa using hpre.2.2.2 v hv⟩
  have hpost := merge_spec o _ _ vs hpre'
  have hm := merge_map o Q p q vs
  simp only [mapP] at hpost hpre'
  rw [hm] at hpost
  have hmem : (x.1, Q x.2) ∈ (merge o p q vs).entries.map (fun x => (x.1, Q x.2)) :=
    List.mem_map.2 ⟨x, hx, rfl⟩
  have h1 := toMap_of_mem o hpost.1 hmem
  rw [hpost.2.1] at h1
  split at h1
  · cases h1
  · have hq' := toMap_mapP Q q x.1
    have hp' := toMap_mapP Q p x.1
    simp only [mapP] at hq' hp'
    rw [hq', hp'] at h1
    cases hq0 : toMap q x.1 with
    | some a =>
      rw [hq0] at h1; simp only [Option.map_some, Option.some_or, Option.some.injEq] at h1
      rw [← h1]; exact hq (x.1, a) (toMap_mem q x.1 a hq0)
    | none =>
      rw [hq0] at h1
      cases hp0 : toMap p x.1 with
      | none => rw [hp0] at h1; cases h1
      | some a =>
        rw [hp0] at h1; simp only [Option.map_none, Option.map_some, Option.none_or, Option.some.injEq] at h1
        rw [← h1]; exact hp (x.1, a) (toMap_mem p x.1 a hp0)
where
  toMap_mem (L : List (K × α)) (k : K) (a : α) (h : toMap L k = some a) : (k, a) ∈ L := by
    induction L with
    | nil => cases h
    | cons y L ih =>
      obtain ⟨k', b⟩ := y
      rw [toMap_cons] at h
      split at h
      · rename_i hk; subst hk; cases h; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

end Helpers

namespace Snap

variable {K D : Type} [DecidableEq K] (o : KeyOrder K)

/-- A concrete snapshot. -/
structure T (K S D : Type) where
  recs : List (K × Slot)
  arena : Arena
  vc : S
  digest : D

def resolve (A : Arena) (s : Slot) : Entry Bytes := (A.read s).getD .tombstone

/-- The entries a concrete snapshot stands for. -/
def entries {S : Type} (s : T K S D) : List (K × Entry Bytes) := mapP (resolve s.arena) s.recs

def isPut : BatchOp K Bytes → Bool
  | .put .. => true
  | .delete .. => false

/-- `Snapshot::apply`'s consensus data: the child and the evicted entries.
`newId` and `compactId` are fresh chunk identities. -/
def apply (X : VCImpl K Bytes D) (p : T K X.S D) (b : List (BatchOp K Bytes)) (victims : List K)
    (newId : Nat) (compactNow : Bool) (compactId : Nat) : T K X.S D × List (K × Entry Bytes) :=
  let packed := Arena.packBatch p.arena.chunks.length b 0
  let arena1 : Arena :=
    if b.any isPut then ⟨p.arena.chunks ++ [⟨newId, packed.1⟩]⟩ else p.arena
  let out := merge o p.recs (Arena.normOps o packed.2) victims
  let vc1 := (out.calls.map (fun c => (c.1, c.2.1.map (resolve arena1), c.2.2.map (resolve arena1)))).foldl
    X.apply p.vc
  let res2 : Arena × List (K × Slot) :=
    if compactNow then Arena.compact arena1 out.entries compactId else (arena1, out.entries)
  let cm := X.commitment vc1 (mapP (resolve res2.1) res2.2)
  (⟨res2.2, res2.1, cm.2, cm.1⟩, mapP (resolve arena1) out.evicted)

/-- A well-formed concrete snapshot for scheme `X` with canonical commitment `F`. -/
def OK (X : VCImpl K Bytes D) (F : List (K × Entry Bytes) → D) (Rep : X.S → List (K × Entry Bytes) → Prop)
    (s : T K X.S D) : Prop :=
  Sorted o s.recs ∧ Arena.WF s.arena s.recs ∧ Rep s.vc (entries s) ∧ s.digest = F (entries s)

/-- Packed slots of a put-free batch are tombstones. -/
theorem pack_noput (ci : Nat) : ∀ (b : List (BatchOp K Bytes)) (off : Nat), b.any isPut = false →
    ∀ x ∈ (Arena.packBatch ci b off).2, x.2 = .tombstone
  | [], _, _, x, hx => by cases hx
  | .put _ _ :: _, _, h, _, _ => by simp [isPut] at h
  | .delete k :: rest, off, h, x, hx => by
    simp only [Arena.packBatch, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rfl
    · exact pack_noput ci rest off (by simpa [isPut] using h) x hx

theorem pack_read_noput (ci : Nat) (A : Arena) : ∀ (b : List (BatchOp K Bytes)) (off : Nat),
    b.any isPut = false →
    (Arena.packBatch ci b off).2.map (fun x => (x.1, A.read x.2)) = b.map (fun op => (op.key, some op.entry))
  | [], _, _ => rfl
  | .put _ _ :: _, _, h => by simp [isPut] at h
  | .delete k :: rest, off, h => by
    simp only [Arena.packBatch, List.map_cons]
    rw [pack_read_noput ci A rest off (by simpa [isPut] using h)]
    rfl

/-- The packed slots read back the batch's entries in the child's arena. -/
theorem packed_read (p : Arena) (b : List (BatchOp K Bytes)) (newId : Nat) :
    (Arena.packBatch p.chunks.length b 0).2.map (fun x => (x.1,
      (if b.any isPut then (⟨p.chunks ++ [⟨newId, (Arena.packBatch p.chunks.length b 0).1⟩]⟩ : Arena)
        else p).read x.2)) = b.map (fun op => (op.key, some op.entry)) := by
  by_cases hput : b.any isPut = true
  · rw [ite_eq_left hput]
    exact Arena.pack_read p.chunks.length _ ⟨newId, (Arena.packBatch p.chunks.length b 0).1⟩
      (by simp) b 0 [] (Nat.zero_le _) (by simp)
  · rw [ite_eq_right hput]
    exact pack_read_noput _ p b 0 (by simpa using hput)

theorem sorted_iff_keys {α : Type} (L : List (K × α)) :
    Sorted o L ↔ (keysL L).Pairwise (fun a b => o.lt a b = true) := by
  simp [Sorted, keysL, List.pairwise_map]

theorem mem_of_mem_normOps {α : Type} (packed : List (K × α)) (x : K × α)
    (hx : x ∈ Arena.normOps o packed) : x ∈ packed := by
  have h := toMap_of_mem o (Arena.sorted_normOps o packed) hx
  rw [Arena.toMap_normOps] at h
  cases hf : packed.reverse.find? (fun y => decide (y.1 = x.1)) with
  | none => rw [hf] at h; cases h
  | some y =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hy := List.mem_reverse.1 (List.mem_of_find?_eq_some hf)
    have hk : y.1 = x.1 := by simpa using List.find?_some hf
    have : y = x := Prod.ext hk h
    rw [← this]; exact hy

/-- **`Snapshot::apply` is correct.** -/
theorem snap_apply (X : VCImpl K Bytes D) (F : List (K × Entry Bytes) → D)
    (Rep : X.S → List (K × Entry Bytes) → Prop) (hX : X.Correct o F Rep)
    (p : T K X.S D) (hp : OK o X F Rep p) (b : List (BatchOp K Bytes)) (victims : List K)
    (hv : victims.Pairwise (fun a c => o.lt a c = true))
    (hvm : ∀ v ∈ victims, v ∈ keysL p.recs ∨ v ∈ b.map BatchOp.key)
    (newId : Nat) (compactNow : Bool) (compactId : Nat) :
    OK o X F Rep (apply o X p b victims newId compactNow compactId).1 ∧
    (∀ k, toMap (entries (apply o X p b victims newId compactNow compactId).1) k =
      childWS (toMap (entries p)) b victims k) ∧
    (apply o X p b victims newId compactNow compactId).2 =
      victims.filterMap (fun v => (finalEntries (toMap (entries p)) b v).map (fun e => (v, e))) := by
  obtain ⟨hsp, hwfp, hrep, _⟩ := hp
  -- names for the stages of `apply`
  let packed := Arena.packBatch p.arena.chunks.length b 0
  let arena1 : Arena := if b.any isPut then ⟨p.arena.chunks ++ [⟨newId, packed.1⟩]⟩ else p.arena
  let ops := Arena.normOps o packed.2
  let out := merge o p.recs ops victims
  let f := resolve arena1
  -- parent slots read the same in the child's arena
  have hpar : ∀ x ∈ p.recs, arena1.read x.2 = p.arena.read x.2 := by
    intro x hx
    by_cases hput : b.any isPut = true
    · show (if b.any isPut then _ else p.arena).read x.2 = _
      rw [ite_eq_left hput]; exact Arena.read_append _ _ _ (hwfp x hx)
    · show (if b.any isPut then _ else p.arena).read x.2 = _
      rw [ite_eq_right hput]
  have hpk := packed_read p.arena b newId
  have hpackedR : mapP f packed.2 = b.map (fun op => (op.key, op.entry)) := by
    have := congrArg (List.map (fun y : K × Option (Entry Bytes) => (y.1, y.2.getD .tombstone))) hpk
    rw [List.map_map, List.map_map] at this
    exact this
  have hops_read : ∀ x ∈ ops, arena1.read x.2 ≠ none := by
    intro x hx
    have hx' := mem_of_mem_normOps o packed.2 x hx
    have : (x.1, arena1.read x.2) ∈ b.map (fun op => (op.key, some op.entry)) := by
      rw [← hpk]; exact List.mem_map.2 ⟨x, hx', rfl⟩
    obtain ⟨op, _, hop⟩ := List.mem_map.1 this
    rw [← (Prod.mk.inj hop).2]; simp
  have hparR : mapP f p.recs = entries p := by
    simp only [mapP, entries, f, resolve]
    apply List.map_congr_left
    intro x hx; rw [hpar x hx]
  have hopsR : ∀ k, toMap (mapP f ops) k = batchFinal b k := by
    intro k
    simp only [ops, mapP]
    rw [Arena.normOps_map, Arena.toMap_normOps, batchFinal_apply]
    have : packed.2.map (fun y => (y.1, f y.2)) = b.map (fun op => (op.key, op.entry)) := hpackedR
    rw [this, ← List.map_reverse, List.find?_map]
    have hpred : ((fun x : K × Entry Bytes => decide (x.1 = k)) ∘ fun op : BatchOp K Bytes => (op.key, op.entry)) =
        (fun o => decide (o.key = k)) := rfl
    rw [hpred]
    cases b.reverse.find? (fun o => decide (o.key = k)) <;> rfl
  have hsops : Sorted o (mapP f ops) := (sorted_mapP o f ops).2 (Arena.sorted_normOps o packed.2)
  have hpre : MPre o (mapP f p.recs) (mapP f ops) victims := by
    refine ⟨(sorted_mapP o f _).2 hsp, hsops, hv, fun v hvv => ?_⟩
    rcases hvm v hvv with h | h
    · exact Or.inl (by simpa using h)
    · right
      rw [← toMap_isSome, hopsR, batchFinal_isSome]; exact h
  have hpost := merge_spec o _ _ victims hpre
  have hm : merge o (mapP f p.recs) (mapP f ops) victims =
      ⟨mapP f out.entries, mapP f out.evicted, out.calls.map (fun c => (c.1, c.2.1.map f, c.2.2.map f))⟩ :=
    merge_map o f p.recs ops victims
  rw [hm] at hpost
  obtain ⟨hS, hT, hE, hC, _⟩ := hpost
  -- the child's records read inside `arena1`
  have hwf1 : Arena.WF arena1 out.entries := by
    intro x hx
    have := merge_entries_pred o (fun s => (arena1.read s).isSome) p.recs ops victims
      ⟨hsp, Arena.sorted_normOps o packed.2, hv, fun v hvv => by
        rcases hvm v hvv with h | h
        · exact Or.inl h
        · right
          rw [← keysL_mapP f ops, ← toMap_isSome, hopsR, batchFinal_isSome]; exact h⟩
      (fun y hy => by rw [hpar y hy]; exact Option.ne_none_iff_isSome.1 (hwfp y hy))
      (fun y hy => Option.ne_none_iff_isSome.1 (hops_read y hy)) x hx
    exact Option.ne_none_iff_isSome.2 this
  -- compaction (or not) keeps keys and entries
  have hres : Sorted o (if compactNow then Arena.compact arena1 out.entries compactId else (arena1, out.entries)).2 ∧
      Arena.WF (if compactNow then Arena.compact arena1 out.entries compactId else (arena1, out.entries)).1
        (if compactNow then Arena.compact arena1 out.entries compactId else (arena1, out.entries)).2 ∧
      mapP (resolve (if compactNow then Arena.compact arena1 out.entries compactId else (arena1, out.entries)).1)
        (if compactNow then Arena.compact arena1 out.entries compactId else (arena1, out.entries)).2 =
        mapP f out.entries := by
    have hso : Sorted o out.entries := (sorted_mapP o f _).1 hS
    split
    · have hd := Arena.compact_decode arena1 out.entries compactId hwf1
      have hkeys : keysL (Arena.compact arena1 out.entries compactId).2 = keysL out.entries := by
        have := congrArg (List.map Prod.fst) hd
        simpa [keysL, Function.comp_def] using this
      refine ⟨(sorted_iff_keys o _).2 (hkeys ▸ (sorted_iff_keys o _).1 hso),
        Arena.compact_wf arena1 out.entries compactId hwf1, ?_⟩
      have := congrArg (List.map (fun y : K × Option (Entry Bytes) => (y.1, y.2.getD .tombstone))) hd
      simpa [mapP, f, resolve, Function.comp_def] using this
    · exact ⟨hso, hwf1, rfl⟩
  obtain ⟨hres1, hres2, hres3⟩ := hres
  have hvc := hX.step p.vc (entries p) (mapP f out.entries)
    (out.calls.map (fun c => (c.1, c.2.1.map f, c.2.2.map f))) hrep
    ((sorted_mapP o _ _).2 hsp) hS (by rw [← hparR]; exact hC)
  have hent : entries (apply o X p b victims newId compactNow compactId).1 = mapP f out.entries := hres3
  have hvcst : (apply o X p b victims newId compactNow compactId).1.vc =
      (X.commitment ((out.calls.map (fun c => (c.1, c.2.1.map f, c.2.2.map f))).foldl X.apply p.vc)
        (mapP f out.entries)).2 := by
    show (X.commitment _ (mapP (resolve
      (if compactNow then Arena.compact arena1 out.entries compactId else (arena1, out.entries)).1)
      (if compactNow then Arena.compact arena1 out.entries compactId else (arena1, out.entries)).2)).2 = _
    rw [hres3]
  have hdig : (apply o X p b victims newId compactNow compactId).1.digest =
      (X.commitment ((out.calls.map (fun c => (c.1, c.2.1.map f, c.2.2.map f))).foldl X.apply p.vc)
        (mapP f out.entries)).1 := by
    show (X.commitment _ (mapP (resolve
      (if compactNow then Arena.compact arena1 out.entries compactId else (arena1, out.entries)).1)
      (if compactNow then Arena.compact arena1 out.entries compactId else (arena1, out.entries)).2)).1 = _
    rw [hres3]
  refine ⟨⟨hres1, hres2, ?_, ?_⟩, ?_, ?_⟩
  · rw [hent, hvcst]; exact hvc.2
  · rw [hent, hdig]; exact hvc.1
  · intro k
    rw [hent, hT k, hparR]
    unfold childWS finalEntries
    rw [hopsR]
  · show mapP f out.evicted = _
    rw [show mapP f out.evicted = _ from hE, hparR]
    apply filterMap_congr_mem
    intro v _
    unfold finalEntries
    rw [hopsR]

/-- The genesis snapshot (`Snapshot::genesis`): no records, an empty arena, a
fresh scheme instance and its commitment of the empty set. -/
def genesis (X : VCImpl K Bytes D) (s0 : X.S) : T K X.S D :=
  ⟨[], ⟨[]⟩, (X.commitment (X.empty s0) []).2, (X.commitment (X.empty s0) []).1⟩

theorem genesis_ok (X : VCImpl K Bytes D) (F : List (K × Entry Bytes) → D)
    (Rep : X.S → List (K × Entry Bytes) → Prop) (hX : X.Correct o F Rep) (s0 : X.S) :
    OK o X F Rep (genesis X s0) := by
  have h := hX.step (X.empty s0) [] [] [] (hX.empty_rep s0) List.Pairwise.nil List.Pairwise.nil
    ⟨List.Pairwise.nil, by simp, by simp⟩
  unfold OK
  refine ⟨List.Pairwise.nil, ?_, h.2, h.1⟩
  intro x hx
  exact absurd hx List.not_mem_nil

end Snap

end RightCash
