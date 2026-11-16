import RightCash.Impl.Sorted

/-!
# `set::merge`: one pass over the parent's records, the batch and the victims

Transcribes the Rust loop of `merge` (src/set.rs) as structural recursion
over the three sorted inputs. The payload type `α` is generic: with entries
it is the write set's meaning, with arena slots it is the snapshot's actual
representation (`RightCash.Impl.Arena`). The loop, step by step:

* take the smaller next key (on equal keys consume both inputs, so the batch
  wins);
* if it is the next victim, omit it from the child, return its final entry for
  storage, and report `apply(key, parent, None)` if the parent had it;
* otherwise keep the batch's slot if any (reporting `apply(key, parent?, new)`),
  or the parent's slot (no report).

`merge_spec` proves that, on sorted inputs whose victims are present, the
output is sorted, stands for the child map (`childWS`), evicts exactly the
victims with their final entries in victim order (the plain path's storage
batch), and reports every changed key exactly once, in ascending order, with
its true old and new entries (the `VectorCommitment::apply` contract).
-/

set_option linter.unusedSectionVars false

namespace RightCash

section Merge
variable {K α : Type} [DecidableEq K] (o : KeyOrder K)

/-- `merge`'s results: the child's records, the evicted final entries, and
the `vc.apply` calls in call order. -/
structure MOut (K α : Type) where
  entries : List (K × α)
  evicted : List (K × α)
  calls : List (K × Option α × Option α)

/-- Keep `key` with slot `fin` (the batch's if any, else the parent's). -/
def retainOut (key : K) (ps bs : Option α) (fin : α) (r : MOut K α) : MOut K α :=
  ⟨(key, fin) :: r.entries, r.evicted, if bs.isSome then (key, ps, bs) :: r.calls else r.calls⟩

/-- Evict `key`, returning its final slot. -/
def evictOut (key : K) (ps : Option α) (fin : α) (r : MOut K α) : MOut K α :=
  ⟨r.entries, (key, fin) :: r.evicted, if ps.isSome then (key, ps, none) :: r.calls else r.calls⟩

/-- One key of the loop: `ps`/`bs` are its parent and batch slots, `vs` the
remaining victims, `rest` the rest of the loop. -/
def emit (key : K) (ps bs : Option α) (fin : α) (vs : List K) (rest : List K → MOut K α) :
    MOut K α :=
  match vs with
  | v :: vt => if v = key then evictOut key ps fin (rest vt) else retainOut key ps bs fin (rest (v :: vt))
  | [] => retainOut key ps bs fin (rest [])

/-- `set::merge(parent, ops, victims, ..)`. -/
def merge : List (K × α) → List (K × α) → List K → MOut K α
  | [], [], _ => ⟨[], [], []⟩
  | [], (k, b) :: ot, vs => emit k none (some b) b vs (fun vs' => merge [] ot vs')
  | (k, a) :: pt, [], vs => emit k (some a) none a vs (fun vs' => merge pt [] vs')
  | (pk, a) :: pt, (ok, b) :: ot, vs =>
    if o.lt pk ok then emit pk (some a) none a vs (fun vs' => merge pt ((ok, b) :: ot) vs')
    else if pk = ok then emit ok (some a) (some b) b vs (fun vs' => merge pt ot vs')
    else emit ok none (some b) b vs (fun vs' => merge ((pk, a) :: pt) ot vs')
termination_by p q _ => p.length + q.length

/-- The `VectorCommitment::apply` contract (design §7.1): calls in strictly
ascending key order, each with the key's true old and new entries, and every
key whose entry differs is reported. -/
def CallsOK (m m' : K → Option α) (calls : List (K × Option α × Option α)) : Prop :=
  calls.Pairwise (fun a b => o.lt a.1 b.1 = true) ∧
  (∀ c ∈ calls, c.2.1 = m c.1 ∧ c.2.2 = m' c.1) ∧
  (∀ k, m k ≠ m' k → k ∈ calls.map Prod.fst)

/-- Preconditions of `merge` (each a Rust `unreachable!` otherwise). -/
def MPre (p q : List (K × α)) (vs : List K) : Prop :=
  Sorted o p ∧ Sorted o q ∧ vs.Pairwise (fun a b => o.lt a b = true) ∧
    ∀ v ∈ vs, v ∈ keysL p ∨ v ∈ keysL q

/-- What `merge` guarantees. -/
def MPost (p q : List (K × α)) (vs : List K) (out : MOut K α) : Prop :=
  Sorted o out.entries ∧
  (∀ k, toMap out.entries k = if k ∈ vs then none else (toMap q k).or (toMap p k)) ∧
  out.evicted = vs.filterMap (fun v => ((toMap q v).or (toMap p v)).map (fun a => (v, a))) ∧
  CallsOK o (toMap p) (toMap out.entries) out.calls ∧
  (∀ c ∈ out.calls, c.1 ∈ keysL p ∨ c.1 ∈ keysL q)

theorem filterMap_congr_mem {β γ : Type} {f g : β → Option γ} :
    ∀ {l : List β}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h x (List.mem_cons_self ..),
      filterMap_congr_mem (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem emit_spec (p q p' q' : List (K × α)) (key : K) (ps bs : Option α) (fin : α)
    (vs : List K) (rest : List K → MOut K α)
    (hpre : MPre o p q vs) (hsp' : Sorted o p') (hsq' : Sorted o q')
    (hgt : ∀ k, k ∈ keysL p' ∨ k ∈ keysL q' → o.lt key k = true)
    (hp : ∀ k, toMap p k = if k = key then ps else toMap p' k)
    (hq : ∀ k, toMap q k = if k = key then bs else toMap q' k)
    (hfin : bs.or ps = some fin)
    (hrest : ∀ vs', MPre o p' q' vs' → MPost o p' q' vs' (rest vs')) :
    MPost o p q vs (emit key ps bs fin vs rest) := by
  obtain ⟨_, _, hvs, hvmem⟩ := hpre
  have hne : ∀ k, (k ∈ keysL p' ∨ k ∈ keysL q') → k ≠ key := fun k hk h => by
    subst h; have := hgt _ hk; rw [o.irrefl] at this; cases this
  have hkeys : ∀ k, k ≠ key → ((k ∈ keysL p ∨ k ∈ keysL q) ↔ (k ∈ keysL p' ∨ k ∈ keysL q')) := by
    intro k hk
    rw [← toMap_isSome, ← toMap_isSome, ← toMap_isSome p', ← toMap_isSome q', hp, hq]
    simp [hk]
  have hf : ∀ k, k ≠ key → (toMap q k).or (toMap p k) = (toMap q' k).or (toMap p' k) := by
    intro k hk; rw [hp, hq]; simp [hk]
  have hfkey : (toMap q key).or (toMap p key) = some fin := by rw [hp, hq]; simpa using hfin
  have hp'key : toMap p' key = none := (toMap_eq_none _ _).2 (fun h => hne key (Or.inl h) rfl)
  have hq'key : toMap q' key = none := (toMap_eq_none _ _).2 (fun h => hne key (Or.inr h) rfl)
  have hpkey : toMap p key = ps := by rw [hp]; simp
  have hkeyin : key ∈ keysL p ∨ key ∈ keysL q := by
    rw [← toMap_isSome, ← toMap_isSome]
    cases h1 : toMap q key <;> cases h2 : toMap p key <;> simp_all
  have hcallsub : ∀ c ∈ (rest vs).calls, True := fun _ _ => trivial
  clear hcallsub
  -- the shared retain case
  have retain : (∀ v ∈ vs, o.lt key v = true) →
      MPost o p q vs (retainOut key ps bs fin (rest vs)) := by
    intro hall
    show MPost o p q vs ⟨(key, fin) :: (rest vs).entries, (rest vs).evicted,
      if bs.isSome then (key, ps, bs) :: (rest vs).calls else (rest vs).calls⟩
    have hpre' : MPre o p' q' vs :=
      ⟨hsp', hsq', hvs, fun v hv => (hkeys v (o.ne_of_lt (hall v hv)).symm).1 (hvmem v hv)⟩
    obtain ⟨R1, R2, R3, ⟨C1, C2, C3⟩, R5⟩ := hrest vs hpre'
    have hkv : key ∉ vs := fun h => by have := hall key h; rw [o.irrefl] at this; cases this
    have hent : ∀ k, toMap ((key, fin) :: (rest vs).entries) k =
        if k ∈ vs then none else (toMap q k).or (toMap p k) := by
      intro k
      rw [toMap_cons]
      by_cases hk : k = key
      · subst hk; simp [hkv, hfkey]
      · rw [ite_eq_right hk, R2, hf k hk]
    have hentkey : ∀ y ∈ (rest vs).entries, o.lt key y.1 = true := by
      intro y hy
      have hs : (toMap (rest vs).entries y.1).isSome :=
        (toMap_isSome _ _).2 (List.mem_map.2 ⟨y, hy, rfl⟩)
      rw [R2] at hs
      by_cases hy' : y.1 ∈ vs
      · simp [hy'] at hs
      · rw [ite_eq_right hy', Option.isSome_or, Bool.or_eq_true, toMap_isSome, toMap_isSome] at hs
        exact hgt _ (Or.comm.1 hs)
    refine ⟨(sorted_cons o).2 ⟨hentkey, R1⟩, hent, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
    · show (rest vs).evicted = _
      rw [R3]
      apply filterMap_congr_mem
      intro v hv
      rw [hf v (o.ne_of_lt (hall v hv)).symm]
    · show List.Pairwise _ (if bs.isSome then (key, ps, bs) :: (rest vs).calls else (rest vs).calls)
      split
      · refine List.pairwise_cons.2 ⟨fun c hc => hgt _ (R5 c hc), C1⟩
      · exact C1
    · show ∀ c ∈ (if bs.isSome then (key, ps, bs) :: (rest vs).calls else (rest vs).calls), _
      have hold : ∀ c ∈ (rest vs).calls,
          c.2.1 = toMap p c.1 ∧ c.2.2 = toMap ((key, fin) :: (rest vs).entries) c.1 := by
        intro c hc
        have hck := hne _ (R5 c hc)
        rw [hp, ite_eq_right hck, toMap_cons, ite_eq_right hck]
        exact C2 c hc
      split
      · rename_i hb
        intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · refine ⟨hpkey.symm, ?_⟩
          rw [toMap_cons, ite_eq_left rfl]
          obtain ⟨b, rfl⟩ := Option.isSome_iff_exists.1 hb
          simpa using hfin
        · exact hold c hc
      · exact hold
    · intro k hk
      have hcalls : ∀ k, k ∈ (rest vs).calls.map Prod.fst →
          k ∈ (if bs.isSome then (key, ps, bs) :: (rest vs).calls else (rest vs).calls).map Prod.fst := by
        intro k hk; split
        · exact List.mem_cons_of_mem _ hk
        · exact hk
      by_cases hkk : k = key
      · subst hkk
        cases hb : bs with
        | none =>
          exfalso; apply hk
          rw [hpkey, toMap_cons, ite_eq_left rfl]
          rw [hb] at hfin; simpa using hfin
        | some b => simp
      · apply hcalls
        apply C3
        rw [hp, ite_eq_right hkk, toMap_cons, ite_eq_right hkk] at hk
        exact hk
    · intro c hc
      have : ∀ c ∈ (rest vs).calls, c.1 ∈ keysL p ∨ c.1 ∈ keysL q :=
        fun c hc => (hkeys _ (hne _ (R5 c hc))).2 (R5 c hc)
      revert hc
      show c ∈ (if bs.isSome then (key, ps, bs) :: (rest vs).calls else (rest vs).calls) → _
      split
      · intro hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact hkeyin
        · exact this c hc
      · exact this c
  cases vs with
  | nil => exact retain (fun _ h => by cases h)
  | cons v vt =>
    have hvt : ∀ v' ∈ vt, o.lt v v' = true := (List.pairwise_cons.1 hvs).1
    by_cases hv : v = key
    · subst hv
      show MPost o p q (v :: vt) (if v = v then _ else _)
      rw [ite_eq_left rfl]
      show MPost o p q (v :: vt) ⟨(rest vt).entries, (v, fin) :: (rest vt).evicted,
        if ps.isSome then (v, ps, none) :: (rest vt).calls else (rest vt).calls⟩
      have hpre' : MPre o p' q' vt :=
        ⟨hsp', hsq', (List.pairwise_cons.1 hvs).2, fun v' hv' =>
          (hkeys v' (o.ne_of_lt (hvt v' hv')).symm).1 (hvmem v' (List.mem_cons_of_mem _ hv'))⟩
      obtain ⟨R1, R2, R3, ⟨C1, C2, C3⟩, R5⟩ := hrest vt hpre'
      have hent : ∀ k, toMap (rest vt).entries k =
          if k ∈ v :: vt then none else (toMap q k).or (toMap p k) := by
        intro k
        rw [R2]
        by_cases hk : k = v
        · subst hk; simp [hp'key, hq'key]
        · simp only [List.mem_cons, hk, false_or]; rw [hf k hk]
      refine ⟨R1, hent, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
      · show (v, fin) :: (rest vt).evicted = _
        rw [List.filterMap_cons, hfkey, R3]
        simp only [Option.map_some]
        congr 1
        apply filterMap_congr_mem
        intro v' hv'
        rw [hf v' (o.ne_of_lt (hvt v' hv')).symm]
      · show List.Pairwise _ (if ps.isSome then (v, ps, none) :: (rest vt).calls else (rest vt).calls)
        split
        · exact List.pairwise_cons.2 ⟨fun c hc => hgt _ (R5 c hc), C1⟩
        · exact C1
      · show ∀ c ∈ (if ps.isSome then (v, ps, none) :: (rest vt).calls else (rest vt).calls), _
        have hold : ∀ c ∈ (rest vt).calls, c.2.1 = toMap p c.1 ∧ c.2.2 = toMap (rest vt).entries c.1 := by
          intro c hc
          rw [hp, ite_eq_right (hne _ (R5 c hc))]
          exact C2 c hc
        split
        · intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · refine ⟨hpkey.symm, ?_⟩
            rw [hent]; simp
          · exact hold c hc
        · exact hold
      · intro k hk
        by_cases hkk : k = v
        · subst hkk
          rw [hent, hpkey] at hk
          simp only [List.mem_cons, true_or, ite_true] at hk
          cases hps : ps with
          | none => exact absurd hps hk
          | some a => simp
        · have : k ∈ (rest vt).calls.map Prod.fst := by
            apply C3
            rw [hp, ite_eq_right hkk] at hk
            exact hk
          split
          · exact List.mem_cons_of_mem _ this
          · exact this
      · intro c hc
        have : ∀ c ∈ (rest vt).calls, c.1 ∈ keysL p ∨ c.1 ∈ keysL q :=
          fun c hc => (hkeys _ (hne _ (R5 c hc))).2 (R5 c hc)
        revert hc
        show c ∈ (if ps.isSome then (v, ps, none) :: (rest vt).calls else (rest vt).calls) → _
        split
        · intro hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact hkeyin
          · exact this c hc
        · exact this c
    · show MPost o p q (v :: vt) (if v = key then _ else _)
      rw [ite_eq_right hv]
      apply retain
      intro v' hv'
      have hvgt : o.lt key v = true :=
        hgt v ((hkeys v hv).1 (hvmem v (List.mem_cons_self ..)))
      rcases List.mem_cons.1 hv' with rfl | hv'
      · exact hvgt
      · exact o.trans _ _ _ hvgt (hvt v' hv')

theorem keysL_gt_of_sorted {k : K} {a : α} {L : List (K × α)} (h : Sorted o ((k, a) :: L)) :
    ∀ k', k' ∈ keysL L → o.lt k k' = true := fun _ hk => lt_of_sorted_cons o h hk

/-- **`merge` is correct.** -/
theorem merge_spec : ∀ (p q : List (K × α)) (vs : List K), MPre o p q vs →
    MPost o p q vs (merge o p q vs)
  | [], [], vs, hpre => by
    have hvs : vs = [] := by
      cases vs with
      | nil => rfl
      | cons v _ => have := hpre.2.2.2 v (List.mem_cons_self ..); simp at this
    subst hvs
    unfold merge
    refine ⟨List.Pairwise.nil, fun k => by simp, rfl, ⟨List.Pairwise.nil, by simp, by simp⟩, by simp⟩
  | [], (k, b) :: ot, vs, hpre => by
    unfold merge
    have hsq := hpre.2.1
    exact emit_spec o [] ((k, b) :: ot) [] ot k none (some b) b vs _ hpre List.Pairwise.nil
      ((sorted_cons o).1 hsq).2
      (fun k' hk' => by
        rcases hk' with h | h
        · simp at h
        · exact keysL_gt_of_sorted o hsq k' h)
      (fun k' => by simp)
      (fun k' => toMap_cons _ _ _ _) rfl
      (fun vs' h => merge_spec [] ot vs' h)
  | (k, a) :: pt, [], vs, hpre => by
    unfold merge
    have hsp := hpre.1
    exact emit_spec o ((k, a) :: pt) [] pt [] k (some a) none a vs _ hpre
      ((sorted_cons o).1 hsp).2 List.Pairwise.nil
      (fun k' hk' => by
        rcases hk' with h | h
        · exact keysL_gt_of_sorted o hsp k' h
        · simp at h)
      (fun k' => toMap_cons _ _ _ _) (fun k' => by simp) rfl
      (fun vs' h => merge_spec pt [] vs' h)
  | (pk, a) :: pt, (ok, b) :: ot, vs, hpre => by
    have hsp := hpre.1
    have hsq := hpre.2.1
    unfold merge
    by_cases hlt : o.lt pk ok = true
    · rw [ite_eq_left hlt]
      exact emit_spec o _ _ pt ((ok, b) :: ot) pk (some a) none a vs _ hpre
        ((sorted_cons o).1 hsp).2 hsq
        (fun k' hk' => by
          rcases hk' with h | h
          · exact keysL_gt_of_sorted o hsp k' h
          · simp only [keysL_cons, List.mem_cons] at h
            rcases h with rfl | h
            · exact hlt
            · exact o.trans _ _ _ hlt (keysL_gt_of_sorted o hsq k' h))
        (fun k' => toMap_cons _ _ _ _)
        (fun k' => by
          by_cases hk : k' = pk
          · subst hk; rw [ite_eq_left rfl]; exact toMap_below_head o hsq hlt
          · rw [ite_eq_right hk])
        rfl
        (fun vs' h => merge_spec pt ((ok, b) :: ot) vs' h)
    · rw [ite_eq_right hlt]
      by_cases heq : pk = ok
      · subst heq
        rw [ite_eq_left rfl]
        exact emit_spec o _ _ pt ot pk (some a) (some b) b vs _ hpre
          ((sorted_cons o).1 hsp).2 ((sorted_cons o).1 hsq).2
          (fun k' hk' => by
            rcases hk' with h | h
            · exact keysL_gt_of_sorted o hsp k' h
            · exact keysL_gt_of_sorted o hsq k' h)
          (fun k' => toMap_cons _ _ _ _) (fun k' => toMap_cons _ _ _ _) rfl
          (fun vs' h => merge_spec pt ot vs' h)
      · rw [ite_eq_right heq]
        have hlt' : o.lt ok pk = true := by
          rcases o.total pk ok heq with h | h
          · exact absurd h hlt
          · exact h
        exact emit_spec o _ _ ((pk, a) :: pt) ot ok none (some b) b vs _ hpre
          hsp ((sorted_cons o).1 hsq).2
          (fun k' hk' => by
            rcases hk' with h | h
            · simp only [keysL_cons, List.mem_cons] at h
              rcases h with rfl | h
              · exact hlt'
              · exact o.trans _ _ _ hlt' (keysL_gt_of_sorted o hsp k' h)
            · exact keysL_gt_of_sorted o hsq k' h)
          (fun k' => by
            by_cases hk : k' = ok
            · subst hk; rw [ite_eq_left rfl]; exact toMap_below_head o hsp hlt'
            · rw [ite_eq_right hk])
          (fun k' => toMap_cons _ _ _ _) rfl
          (fun vs' h => merge_spec ((pk, a) :: pt) ot vs' h)
termination_by p q _ => p.length + q.length

/-- `merge` commutes with any map over payloads (it only compares keys). -/
theorem merge_map {β : Type} (f : α → β) : ∀ (p q : List (K × α)) (vs : List K),
    merge o (p.map (fun x => (x.1, f x.2))) (q.map (fun x => (x.1, f x.2))) vs =
      let r := merge o p q vs
      ⟨r.entries.map (fun x => (x.1, f x.2)), r.evicted.map (fun x => (x.1, f x.2)),
        r.calls.map (fun c => (c.1, c.2.1.map f, c.2.2.map f))⟩
  | [], [], vs => by unfold merge; rfl
  | [], (k, b) :: ot, vs => by
    simp only [List.map_cons, List.map_nil]
    unfold merge
    have ih := fun vs' => merge_map f [] ot vs'
    simp only [List.map_nil] at ih
    cases vs with
    | nil => simp [emit, retainOut, ih]
    | cons v vt => by_cases hv : v = k <;> simp [emit, retainOut, evictOut, hv, ih]
  | (k, a) :: pt, [], vs => by
    simp only [List.map_cons, List.map_nil]
    unfold merge
    have ih := fun vs' => merge_map f pt [] vs'
    simp only [List.map_nil] at ih
    cases vs with
    | nil => simp [emit, retainOut, ih]
    | cons v vt => by_cases hv : v = k <;> simp [emit, retainOut, evictOut, hv, ih]
  | (pk, a) :: pt, (ok, b) :: ot, vs => by
    simp only [List.map_cons]
    unfold merge
    have ih1 := fun vs' => merge_map f pt ((ok, b) :: ot) vs'
    have ih2 := fun vs' => merge_map f pt ot vs'
    have ih3 := fun vs' => merge_map f ((pk, a) :: pt) ot vs'
    simp only [List.map_cons] at ih1 ih3
    by_cases hlt : o.lt pk ok = true
    · simp only [hlt, ite_true]
      cases vs with
      | nil => simp [emit, retainOut, ih1]
      | cons v vt => by_cases hv : v = pk <;> simp [emit, retainOut, evictOut, hv, ih1]
    · simp only [hlt, Bool.false_eq_true, ite_false]
      by_cases heq : pk = ok
      · subst heq
        simp only [ite_true]
        cases vs with
        | nil => simp [emit, retainOut, ih2]
        | cons v vt => by_cases hv : v = pk <;> simp [emit, retainOut, evictOut, hv, ih2]
      · simp only [heq, ite_false]
        cases vs with
        | nil => simp [emit, retainOut, ih3]
        | cons v vt => by_cases hv : v = ok <;> simp [emit, retainOut, evictOut, hv, ih3]
termination_by p q _ => p.length + q.length

end Merge

end RightCash
