import RightCash.Basic

/-!
# The speculation worker

Models `src/speculate.rs` (design §9.2). The worker owns one *chain*: the
base view it started from, the latest speculative view, the pending map of
ops not yet hashed into a step, and a failure flag.

Modelling choices (all of them over-approximate the Rust behaviours):

* Requests reach the worker through a FIFO channel and it handles them one at
  a time, so each request is applied atomically, in order.
* Whether and when the worker builds an early step depends on `min_step`,
  `rounds` and timing; the model lets a step be built (or fail) *at any
  time* the chain is healthy and has pending ops (`Engine.workerStep`).
* Every storage call the worker makes may fail (`ProposalOrphaned`, a stale
  read, an I/O error, a caught panic); the model lets any build fail.
* A pending map is a list with replace-on-insert semantics
  (`BTreeMap::insert`). The ops of one step are applied oldest-first; since
  the map has one op per key, the order is immaterial on a correct engine.
-/

set_option linter.unusedSectionVars false

namespace RightCash

/-- `speculate::SpecOp`. -/
inductive SpecOp (K V : Type) where
  /-- Write the entry to storage early. -/
  | evict (k : K) (e : Entry V)
  /-- Put back what the chain base holds for the key. -/
  | retract (k : K)

namespace SpecOp
variable {K V : Type}

def key : SpecOp K V → K
  | evict k _ => k
  | retract k => k

/-- `build_step`: evictions become `Put`/`Delete`; a retraction reads the chain
*base* (`put_back`). -/
def toOp (base : Store K V) : SpecOp K V → BatchOp K V
  | evict k e => BatchOp.ofEntry k e
  | retract k => BatchOp.ofOption k (base k)

/-- The op's effect on storage at its key. -/
def effect (base : Store K V) : SpecOp K V → Option V
  | evict _ e => e.toStore
  | retract k => base k

@[simp] theorem key_toOp (base : Store K V) (op : SpecOp K V) : (op.toOp base).key = op.key := by
  cases op <;> simp [toOp, key]

@[simp] theorem val_toOp (base : Store K V) (op : SpecOp K V) :
    (op.toOp base).val = op.effect base := by
  cases op <;> simp [toOp, effect]

end SpecOp

section Pending
variable {K V : Type} [DecidableEq K]

/-- `BTreeMap::insert`: the new op replaces any op on the same key. -/
def pinsert (p : List (SpecOp K V)) (op : SpecOp K V) : List (SpecOp K V) :=
  op :: p.filter (fun q => decide (q.key ≠ op.key))

/-- Lookup in the pending map. -/
def plookup (p : List (SpecOp K V)) (k : K) : Option (SpecOp K V) :=
  p.find? (fun q => decide (q.key = k))

theorem plookup_pinsert (p : List (SpecOp K V)) (op : SpecOp K V) (k : K) :
    plookup (pinsert p op) k = if op.key = k then some op else plookup p k := by
  unfold plookup pinsert
  rw [List.find?_cons]
  by_cases h : op.key = k
  · simp [h]
  · simp only [h, decide_false, ite_false]
    rw [List.find?_filter]
    congr 1
    funext q
    by_cases hq : q.key = k
    · subst hq; simp [Ne.symm h]
    · simp [hq]

theorem plookup_foldl (ops p : List (SpecOp K V)) (k : K) :
    plookup (ops.foldl pinsert p) k =
      (ops.reverse.find? (fun q => decide (q.key = k))).or (plookup p k) := by
  induction ops generalizing p with
  | nil => simp
  | cons op ops ih =>
    rw [List.foldl_cons, ih, plookup_pinsert, List.reverse_cons, List.find?_append,
      Option.or_assoc]
    congr 1
    by_cases h : op.key = k <;> simp [h]

end Pending

/-! ## Finding ops by key -/

section SpecOps
variable {K V : Type} [DecidableEq K]

/-- `spec_ops` in `lib.rs` (and the final-op construction in
`finish_speculation`): an `Evict` with the entry for each key of `E`, then a
`Retract` for each key of `R`. A key of `E` without an entry would make the
Rust code panic; the model drops it (the proofs show it never happens where
it matters). -/
def specOps (ws : WriteSet K V) (E R : List K) : List (SpecOp K V) :=
  E.filterMap (fun k => (ws k).map (SpecOp.evict k)) ++ R.map SpecOp.retract

theorem specOps_find (ws : WriteSet K V) (E R : List K) (k : K) :
    (specOps ws E R).reverse.find? (fun q => decide (q.key = k)) =
      if k ∈ R then some (.retract k) else if k ∈ E then (ws k).map (.evict k) else none := by
  unfold specOps
  rw [List.reverse_append, List.find?_append]
  have hR : (R.map (SpecOp.retract (V := V))).reverse.find? (fun q => decide (q.key = k)) =
      if k ∈ R then some (.retract k) else none := by
    by_cases hk : k ∈ R
    · rw [ite_eq_left hk]
      apply find?_eq_some_of_unique
      · intro x hx hpx
        simp only [List.mem_reverse, List.mem_map] at hx
        obtain ⟨k', _, rfl⟩ := hx
        simp only [SpecOp.key] at hpx; replace hpx := of_decide_eq_true hpx
        rw [hpx]
      · simp only [List.mem_reverse, List.mem_map]; exact ⟨k, hk, rfl⟩
      · simp [SpecOp.key]
    · rw [ite_eq_right hk, List.find?_eq_none]
      intro x hx hpx
      simp only [List.mem_reverse, List.mem_map] at hx
      obtain ⟨k', hk', rfl⟩ := hx
      simp only [SpecOp.key] at hpx; replace hpx := of_decide_eq_true hpx
      exact hk (hpx ▸ hk')
  have hE : (E.filterMap (fun k => (ws k).map (SpecOp.evict k))).reverse.find?
      (fun q => decide (q.key = k)) = if k ∈ E then (ws k).map (.evict k) else none := by
    have hmemE : ∀ x, x ∈ (E.filterMap (fun k => (ws k).map (SpecOp.evict k))).reverse ↔
        ∃ k', k' ∈ E ∧ ∃ e, ws k' = some e ∧ x = .evict k' e := by
      intro x
      simp only [List.mem_reverse, List.mem_filterMap, Option.map_eq_some_iff]
      constructor
      · rintro ⟨k', hk', e, he, rfl⟩; exact ⟨k', hk', e, he, rfl⟩
      · rintro ⟨k', hk', e, he, rfl⟩; exact ⟨k', hk', e, he, rfl⟩
    by_cases hk : k ∈ E
    · rw [ite_eq_left hk]
      cases hw : ws k with
      | none =>
        simp only [Option.map_none]
        rw [List.find?_eq_none]
        intro x hx hpx
        obtain ⟨k', _, e, he, rfl⟩ := (hmemE x).1 hx
        simp only [SpecOp.key] at hpx; replace hpx := of_decide_eq_true hpx
        subst hpx; rw [hw] at he; cases he
      | some e =>
        simp only [Option.map_some]
        apply find?_eq_some_of_unique
        · intro x hx hpx
          obtain ⟨k', _, e', he', rfl⟩ := (hmemE x).1 hx
          simp only [SpecOp.key] at hpx; replace hpx := of_decide_eq_true hpx
          subst hpx; rw [hw] at he'; cases he'; rfl
        · exact (hmemE _).2 ⟨k, hk, e, hw, rfl⟩
        · simp [SpecOp.key]
    · rw [ite_eq_right hk, List.find?_eq_none]
      intro x hx hpx
      obtain ⟨k', hk', e, _, rfl⟩ := (hmemE x).1 hx
      simp only [SpecOp.key] at hpx; replace hpx := of_decide_eq_true hpx
      exact hk (hpx ▸ hk')
  rw [hR, hE]
  by_cases h1 : k ∈ R <;> by_cases h2 : k ∈ E <;> simp [h1, h2]

end SpecOps

/-! ## Chains -/

/-- `speculate::Chain`. `failed` is `status.is_err()`. -/
structure Chain (K V : Type) where
  base : Store K V
  latest : Store K V
  pending : List (SpecOp K V)
  failed : Bool
  steps : Nat

namespace Chain
variable {K V : Type} [DecidableEq K]

/-- `Chain::new(base)` (a `Reset`, or the worker's start). -/
def new (base : Store K V) : Chain K V := ⟨base, base, [], false, 0⟩

/-- `Chain::merge` (a `Submit` or block end): a failed chain drops the ops. -/
def submit (c : Chain K V) (ops : List (SpecOp K V)) : Chain K V :=
  if c.failed then c else { c with pending := ops.foldl pinsert c.pending }

/-- The batch of one step: the pending ops as storage ops. -/
def batch (c : Chain K V) : List (BatchOp K V) := c.pending.reverse.map (SpecOp.toOp c.base)

/-- A successful `Chain::build`: one storage proposal on `latest`. -/
def build (c : Chain K V) : Chain K V :=
  { c with latest := applyBatch c.latest c.batch, pending := [], steps := c.steps + 1 }

/-- A failed `Chain::build`: the taken ops are lost and the chain is unusable. -/
def fail (c : Chain K V) : Chain K V := { c with pending := [], failed := true }

/-- `Chain::finish`: merge the final ops, build at most one more proposal
(which may fail: `ok = false`), and return the final view, or `none` on
failure (the writer then takes the plain path). -/
def finish (c : Chain K V) (ops : List (SpecOp K V)) (md : Option (List UInt8)) (ok : Bool) :
    Option (Store K V) :=
  let c1 := c.submit ops
  if c1.failed then none
  else if c1.pending ≠ [] ∨ md.isSome ∨ c1.steps = 0 then
    (if ok then some c1.build.latest else none)
  else some c1.latest

/-- The storage state the chain stands for: `latest` with the pending ops
applied. Building a step never changes it. -/
def eff (c : Chain K V) (k : K) : Option V :=
  (plookup c.pending k).elim (c.latest k) (SpecOp.effect c.base)

@[simp] theorem eff_new (s : Store K V) (k : K) : (new s).eff k = s k := by
  simp [eff, new, plookup]

@[simp] theorem submit_base (c : Chain K V) (ops) : (c.submit ops).base = c.base := by
  unfold submit; split <;> rfl

@[simp] theorem submit_failed (c : Chain K V) (ops) : (c.submit ops).failed = c.failed := by
  unfold submit; split <;> rfl

@[simp] theorem build_base (c : Chain K V) : c.build.base = c.base := rfl
@[simp] theorem build_failed (c : Chain K V) : c.build.failed = c.failed := rfl
@[simp] theorem fail_base (c : Chain K V) : c.fail.base = c.base := rfl
@[simp] theorem fail_failed (c : Chain K V) : c.fail.failed = true := rfl

theorem build_latest (c : Chain K V) (k : K) : c.build.latest k = c.eff k := by
  simp only [build, eff, batch]
  rw [applyBatch_apply, ← List.map_reverse, List.reverse_reverse, List.find?_map]
  unfold plookup
  have : ((fun o : BatchOp K V => decide (o.key = k)) ∘ SpecOp.toOp c.base) =
      (fun q : SpecOp K V => decide (q.key = k)) := by
    funext q; simp
  rw [this]
  cases c.pending.find? (fun q => decide (q.key = k)) <;> simp

theorem eff_build (c : Chain K V) (k : K) : c.build.eff k = c.eff k := by
  have h : c.build.eff k = c.build.latest k := by simp [eff, plookup, build]
  rw [h, build_latest]

theorem eff_submit (c : Chain K V) (ops : List (SpecOp K V)) (hc : c.failed = false) (k : K) :
    (c.submit ops).eff k =
      (ops.reverse.find? (fun q => decide (q.key = k))).elim (c.eff k) (SpecOp.effect c.base) := by
  simp only [submit, hc, Bool.false_eq_true, ite_false, eff]
  rw [plookup_foldl]
  cases ops.reverse.find? (fun q => decide (q.key = k)) <;> simp

/-- Submitting `spec_ops`: a retraction restores the base; an eviction writes
the entry; any other key keeps its effective value. -/
theorem eff_submit_specOps (c : Chain K V) (ws : WriteSet K V) (E R : List K)
    (hc : c.failed = false) (k : K) :
    (c.submit (specOps ws E R)).eff k =
      if k ∈ R then c.base k
      else if k ∈ E then (ws k).elim (c.eff k) Entry.toStore
      else c.eff k := by
  rw [eff_submit c _ hc, specOps_find]
  by_cases h1 : k ∈ R
  · simp [h1, SpecOp.effect]
  · by_cases h2 : k ∈ E
    · cases ws k <;> simp [h1, h2, SpecOp.effect]
    · simp [h1, h2]

/-- A successful `finish` returns the effective state of the chain after
merging the final ops. -/
theorem finish_some (c : Chain K V) (ops : List (SpecOp K V)) (md : Option (List UInt8))
    (ok : Bool) (st : Store K V) (h : c.finish ops md ok = some st) :
    c.failed = false ∧ ∀ k, st k = (c.submit ops).eff k := by
  unfold finish at h
  simp only at h
  by_cases hf : (c.submit ops).failed = true
  · rw [ite_eq_left hf] at h; cases h
  · rw [ite_eq_right hf] at h
    refine ⟨by simpa using hf, ?_⟩
    split at h
    · split at h
      · cases h; intro k; exact build_latest _ k
      · cases h
    · cases h
      rename_i hcond
      have hp : (c.submit ops).pending = [] := by
        cases h' : (c.submit ops).pending with
        | nil => rfl
        | cons _ _ => exact absurd (Or.inl (by rw [h']; simp)) hcond
      intro k
      simp [eff, hp, plookup]

end Chain

end RightCash
