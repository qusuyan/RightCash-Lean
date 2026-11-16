import RightCash.Impl.Merge

/-!
# Vector commitments: framework, `rehash`, `lthash`

The `VectorCommitment` trait (src/vc/mod.rs): a scheme instance is cloned
from the parent's, receives one `apply(key, old, new)` per changed key (the
calls `merge` makes, `merge_spec`), then `commitment(entries)` over the
child's entries in ascending key order.

`VCImpl.Correct X F Rep` says that the instance state `Rep`resents the set
it was built for, and that the digest produced after any correct sequence of
`apply` calls is `F L'`, a function of the child's sorted entry list alone.
Together with `sorted_ext` this makes the stored commitment a function of
the write set, which discharges assumption A3 of SPEC.md for the scheme.

Hash functions stay uninterpreted (SPEC.md §3); for `lthash` only the
abelian-group laws of the lane vector are used.
-/

set_option linter.unusedSectionVars false

namespace RightCash

/-- One `apply(key, old, new)` call. -/
abbrev Change (K V : Type) := K × Option (Entry V) × Option (Entry V)

/-- A `VectorCommitment` implementation. -/
structure VCImpl (K V D : Type) where
  S : Type
  /-- `VectorCommitment::empty(&self)`. -/
  empty : S → S
  apply : S → Change K V → S
  /-- `commitment(&mut self, entries)`: digest and updated instance. -/
  commitment : S → List (K × Entry V) → D × S

section Framework
variable {K V D : Type} [DecidableEq K] (o : KeyOrder K)

/-- Correctness of a scheme with respect to the canonical commitment `F`. -/
structure VCImpl.Correct (X : VCImpl K V D) (F : List (K × Entry V) → D)
    (Rep : X.S → List (K × Entry V) → Prop) : Prop where
  empty_rep : ∀ s, Rep (X.empty s) []
  step : ∀ (s : X.S) (L L' : List (K × Entry V)) (calls : List (Change K V)),
    Rep s L → Sorted o L → Sorted o L' → CallsOK o (toMap L) (toMap L') calls →
    (X.commitment (calls.foldl X.apply s) L').1 = F L' ∧
      Rep (X.commitment (calls.foldl X.apply s) L').2 L'

/-- The commitment of a correct scheme depends only on the set. -/
theorem VCImpl.digest_of_set (F : List (K × Entry V) → D) {L₁ L₂ : List (K × Entry V)}
    (h₁ : Sorted o L₁) (h₂ : Sorted o L₂) (h : ∀ k, toMap L₁ k = toMap L₂ k) : F L₁ = F L₂ := by
  rw [sorted_ext o h₁ h₂ h]

/-- Sorted record lists have distinct keys. -/
theorem nodup_keysL_of_sorted {α : Type} {L : List (K × α)} (h : Sorted o L) : (keysL L).Nodup := by
  unfold keysL Sorted at *
  rw [List.Nodup, List.pairwise_map]
  exact h.imp (fun hlt heq => o.ne_of_lt hlt heq)

/-- After a correct sequence of calls, the "current map" is the child's. -/
theorem calls_fold_map {α : Type} (m m' : K → Option α) (calls : List (K × Option α × Option α))
    (h : CallsOK o m m' calls) :
    calls.foldl (fun f c => fupd f c.1 c.2.2) m = m' := by
  funext k
  rw [foldl_fupd_apply (fun c : K × Option α × Option α => c.1) (fun c => c.2.2)]
  cases hf : calls.reverse.find? (fun c => decide (c.1 = k)) with
  | some c =>
    have hc : c ∈ calls := List.mem_reverse.1 (List.mem_of_find?_eq_some hf)
    have hk : c.1 = k := by simpa using List.find?_some hf
    simp only [Option.elim_some]
    rw [(h.2.1 c hc).2, hk]
  | none =>
    simp only [Option.elim_none]
    by_cases hd : m k = m' k
    · exact hd
    · exfalso
      obtain ⟨c, hc, hck⟩ := List.mem_map.1 (h.2.2 k hd)
      exact List.find?_eq_none.1 hf c (List.mem_reverse.2 hc) (by simpa using hck)

end Framework

/-! ## `rehash`: one hash over the whole set -/

section Rehash
variable {K V D : Type} [DecidableEq K] (o : KeyOrder K)

/-- `vc::rehash::Rehash`: no state; `commitment` hashes every entry in order
(`H` = BLAKE3 `derive_key` over the count and the length-prefixed items). -/
def rehash (H : List (K × Entry V) → D) : VCImpl K V D :=
  ⟨Unit, fun _ => (), fun s _ => s, fun s L => (H L, s)⟩

theorem rehash_correct (H : List (K × Entry V) → D) :
    (rehash H).Correct o H (fun _ _ => True) :=
  ⟨fun _ => trivial, fun _ _ _ _ _ _ _ _ => ⟨rfl, trivial⟩⟩

end Rehash

/-! ## `lthash`: the lattice accumulator -/

/-- The abelian-group laws the lattice lanes satisfy (lane-wise wrapping
arithmetic on `u16`). -/
structure AbGroup (G : Type) where
  zero : G
  add : G → G → G
  neg : G → G
  add_comm : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_zero : ∀ a, add a zero = a
  add_neg : ∀ a, add a (neg a) = zero

/-- The lattice lanes, `[u16; n]` with wrapping lane-wise addition. -/
def lanes (n : Nat) : AbGroup (Fin n → UInt16) where
  zero := fun _ => 0
  add := fun a b i => a i + b i
  neg := fun a i => -a i
  add_comm a b := funext fun i => UInt16.add_comm _ _
  add_assoc a b c := funext fun i => UInt16.add_assoc _ _ _
  add_zero a := funext fun i => UInt16.add_zero _
  add_neg a := funext fun i => by
    show a i + -a i = 0
    rw [← UInt16.sub_eq_add_neg, UInt16.sub_self]

namespace AbGroup
variable {G : Type} (A : AbGroup G)

theorem add_neg_cancel_right (x a : G) : A.add (A.add x a) (A.neg a) = x := by
  rw [A.add_assoc, A.add_neg, A.add_zero]

theorem add_right_comm (x a b : G) : A.add (A.add x a) b = A.add (A.add x b) a := by
  rw [A.add_assoc, A.add_comm a b, ← A.add_assoc]

end AbGroup

/-- The pieces of `vc::lthash::LtHash`: the item hash (ChaCha8 expansion of
the BLAKE3 hash of the entry item) and the final digest (SHA-256 of the lanes). -/
structure LtParams (K V D G : Type) where
  grp : AbGroup G
  item : K → Entry V → G
  digest : G → D

section LtHash
variable {K V D G : Type} [DecidableEq K] (o : KeyOrder K) (Q : LtParams K V D G)

def LtParams.itemOpt (k : K) : Option (Entry V) → G
  | some e => Q.item k e
  | none => Q.grp.zero

/-- `lthash` as a scheme: `apply` removes the old item and adds the new one. -/
def lthash : VCImpl K V D where
  S := G
  empty := fun _ => Q.grp.zero
  apply := fun s c => Q.grp.add (Q.grp.add s (Q.grp.neg (Q.itemOpt c.1 c.2.1))) (Q.itemOpt c.1 c.2.2)
  commitment := fun s _ => (Q.digest s, s)

/-- The sum of the items of a set. -/
def LtParams.sumL (L : List (K × Entry V)) : G := L.foldr (fun x acc => Q.grp.add (Q.item x.1 x.2) acc) Q.grp.zero

/-- The sum of `f` over a list of keys. -/
def LtParams.sumKeys (f : K → G) (U : List K) : G := U.foldr (fun k acc => Q.grp.add (f k) acc) Q.grp.zero

@[simp] theorem sumL_nil : Q.sumL ([] : List (K × Entry V)) = Q.grp.zero := rfl
@[simp] theorem sumL_cons (k : K) (e : Entry V) (L : List (K × Entry V)) :
    Q.sumL ((k, e) :: L) = Q.grp.add (Q.item k e) (Q.sumL L) := rfl
@[simp] theorem sumKeys_nil (f : K → G) : Q.sumKeys f [] = Q.grp.zero := rfl
@[simp] theorem sumKeys_cons (f : K → G) (k : K) (U : List K) :
    Q.sumKeys f (k :: U) = Q.grp.add (f k) (Q.sumKeys f U) := rfl

theorem sumKeys_congr (f g : K → G) : ∀ (U : List K), (∀ k ∈ U, f k = g k) → Q.sumKeys f U = Q.sumKeys g U
  | [], _ => rfl
  | k :: U, h => by
    rw [sumKeys_cons, sumKeys_cons, h k (List.mem_cons_self ..),
      sumKeys_congr f g U (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))]

theorem sumKeys_zero : ∀ (U : List K), Q.sumKeys (fun _ => Q.grp.zero) U = Q.grp.zero
  | [] => rfl
  | k :: U => by rw [sumKeys_cons, sumKeys_zero U, Q.grp.add_zero]

/-- Telescoping: changing one key's entry changes the sum by the item difference. -/
theorem sumKeys_fupd (m : K → Option (Entry V)) (k : K) (e : Option (Entry V)) :
    ∀ (U : List K), U.Nodup → k ∈ U →
      Q.grp.add (Q.sumKeys (fun j => Q.itemOpt j (fupd m k e j)) U) (Q.itemOpt k (m k)) =
        Q.grp.add (Q.sumKeys (fun j => Q.itemOpt j (m j)) U) (Q.itemOpt k e)
  | [], _, h => absurd h List.not_mem_nil
  | u :: U, hnd, hk => by
    obtain ⟨hu, hnd'⟩ := List.nodup_cons.1 hnd
    rw [sumKeys_cons, sumKeys_cons]
    by_cases huk : u = k
    · subst huk
      have hrest : Q.sumKeys (fun j => Q.itemOpt j (fupd m u e j)) U =
          Q.sumKeys (fun j => Q.itemOpt j (m j)) U :=
        sumKeys_congr Q _ _ U (fun j hj => by
          rw [fupd_ne _ _ (by intro h; subst h; exact hu hj)])
      rw [hrest, fupd_same, Q.grp.add_comm (Q.itemOpt u e), Q.grp.add_comm (Q.itemOpt u (m u)),
        Q.grp.add_assoc, Q.grp.add_comm (Q.itemOpt u e), Q.grp.add_assoc]
    · have hk' : k ∈ U := by
        rcases List.mem_cons.1 hk with h | h
        · exact absurd h.symm huk
        · exact h
      rw [fupd_ne _ _ huk, Q.grp.add_assoc, sumKeys_fupd m k e U hnd' hk', ← Q.grp.add_assoc]

/-- The sum over a sorted set equals its sum over any key universe containing it. -/
theorem sumL_eq_sumKeys (U : List K) (hU : U.Nodup) :
    ∀ (L : List (K × Entry V)), Sorted o L → (∀ k ∈ keysL L, k ∈ U) →
      Q.sumL L = Q.sumKeys (fun j => Q.itemOpt j (toMap L j)) U
  | [], _, _ => by
    rw [sumL_nil, sumKeys_congr Q (fun j => Q.itemOpt j (toMap ([] : List (K × Entry V)) j))
      (fun _ => Q.grp.zero) U (fun j _ => rfl), sumKeys_zero]
  | (k, e) :: L, hs, hsub => by
    have hsL := ((sorted_cons o).1 hs).2
    have hkL : k ∉ keysL L := not_mem_tail_of_sorted o hs
    have ih := sumL_eq_sumKeys U hU L hsL (fun j hj => hsub j (List.mem_cons_of_mem _ hj))
    have hmap : (fun j => Q.itemOpt j (toMap ((k, e) :: L) j)) =
        (fun j => Q.itemOpt j (fupd (toMap L) k (some e) j)) := by
      funext j; rw [toMap_cons]; by_cases hj : j = k
      · subst hj; simp
      · rw [ite_eq_right hj, fupd_ne _ _ hj]
    rw [hmap]
    have tel := sumKeys_fupd Q (toMap L) k (some e) U hU (hsub k (List.mem_cons_self ..))
    rw [(toMap_eq_none L k).2 hkL,
      show Q.itemOpt k (none : Option (Entry V)) = Q.grp.zero from rfl, Q.grp.add_zero,
      show Q.itemOpt k (some e) = Q.item k e from rfl] at tel
    rw [sumL_cons, tel, ← ih, Q.grp.add_comm]

/-- Applying a correct sequence of calls moves the accumulator along the map. -/
theorem lthash_fold (U : List K) (hU : U.Nodup) :
    ∀ (calls : List (Change K V)) (m : K → Option (Entry V)) (s : G),
      calls.Pairwise (fun a b => o.lt a.1 b.1 = true) →
      (∀ c ∈ calls, c.1 ∈ U ∧ c.2.1 = m c.1) →
      s = Q.sumKeys (fun j => Q.itemOpt j (m j)) U →
      List.foldl (lthash Q).apply s calls =
        Q.sumKeys (fun j => Q.itemOpt j ((calls.foldl (fun f c => fupd f c.1 c.2.2) m) j)) U
  | [], _, _, _, _, hs => hs
  | c :: cs, m, s, hp, hc, hs => by
    obtain ⟨hlt, hp'⟩ := List.pairwise_cons.1 hp
    obtain ⟨hcU, hold⟩ := hc c (List.mem_cons_self ..)
    show List.foldl (lthash Q).apply ((lthash Q).apply s c) cs =
      Q.sumKeys (fun j => Q.itemOpt j ((cs.foldl (fun f c => fupd f c.1 c.2.2) (fupd m c.1 c.2.2)) j)) U
    apply lthash_fold U hU cs (fupd m c.1 c.2.2) _ hp'
    · intro c' hc'
      refine ⟨(hc c' (List.mem_cons_of_mem _ hc')).1, ?_⟩
      rw [fupd_ne _ _ (o.ne_of_lt (hlt c' hc')).symm]
      exact (hc c' (List.mem_cons_of_mem _ hc')).2
    · have tel := sumKeys_fupd Q m c.1 c.2.2 U hU hcU
      show Q.grp.add (Q.grp.add s (Q.grp.neg (Q.itemOpt c.1 c.2.1))) (Q.itemOpt c.1 c.2.2) = _
      rw [hold, hs, ← Q.grp.add_neg_cancel_right
        (Q.sumKeys (fun j => Q.itemOpt j (fupd m c.1 c.2.2 j)) U) (Q.itemOpt c.1 (m c.1)), tel]
      exact Q.grp.add_right_comm _ _ _

/-- **`lthash` is correct**: the incrementally maintained accumulator always
equals the sum of the items of the current set. -/
theorem lthash_correct :
    (lthash Q).Correct o (fun L => Q.digest (Q.sumL L)) (fun s L => s = Q.sumL L) := by
  refine ⟨fun _ => rfl, fun s L L' calls hrep hs hs' hc => ?_⟩
  let U := dedup (keysL L ++ keysL L' ++ calls.map Prod.fst)
  have hU : U.Nodup := nodup_dedup _
  have hL : ∀ k ∈ keysL L, k ∈ U :=
    fun k hk => mem_dedup.2 (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hk))))
  have hs0 : s = Q.sumKeys (fun j => Q.itemOpt j (toMap L j)) U := by
    rw [hrep]; exact sumL_eq_sumKeys o Q U hU L hs hL
  have hcalls : ∀ c ∈ calls, c.1 ∈ U ∧ c.2.1 = toMap L c.1 :=
    fun c hcm => ⟨mem_dedup.2 (List.mem_append.2 (Or.inr (List.mem_map.2 ⟨c, hcm, rfl⟩))),
      (hc.2.1 c hcm).1⟩
  have hfold := lthash_fold o Q U hU calls (toMap L) s hc.1 hcalls hs0
  rw [calls_fold_map o _ _ calls hc] at hfold
  have hfin : List.foldl (lthash Q).apply s calls = Q.sumL L' := by
    rw [hfold, sumL_eq_sumKeys o Q U hU L' hs'
      (fun k hk => mem_dedup.2 (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hk)))))]
  exact ⟨congrArg Q.digest hfin, hfin⟩

end LtHash

end RightCash
