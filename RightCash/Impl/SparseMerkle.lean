import RightCash.Impl.VC

/-!
# The sparse Merkle tree scheme (`src/vc/merkle.rs`)

Leaves sit at depth `DEPTH = 256`, addressed by the bits of `SHA-256(key)`.
The instance stores the non-default node hashes by position `(level,
prefix)`; `apply` rewrites the leaf of the key and recomputes its path,
reading siblings from the map (absent = the level's default hash).

`up_spec` shows that the path update keeps every stored position equal to
the recursive subtree hash (`sub`, the `oracle` of the Rust tests);
`smt_correct` lifts it to `VCImpl.Correct`. As in the Rust documentation,
distinct keys are assumed to have distinct addresses (`Function.Injective
addr`); a violation is a SHA-256 collision.
-/

set_option linter.unusedSectionVars false

namespace RightCash
namespace SMT

/-- The scheme's hash functions. Positions use prefixes as bit lists
(`prefix(path, level)` of the Rust code, without the zero padding). -/
structure Params (K V D : Type) where
  depth : Nat
  addr : K → List Bool
  addr_length : ∀ k, (addr k).length = depth
  leaf : K → Entry V → D
  inner : D → D → D
  emptyLeaf : D

variable {K V D : Type} [DecidableEq K] [DecidableEq D] (P : Params K V D)

/-- `defaults()`, indexed by subtree height. -/
def dflt : Nat → D
  | 0 => P.emptyLeaf
  | h + 1 => P.inner (dflt h) (dflt h)

/-- The hash of the subtree of height `h` under prefix `p`. -/
def sub (lf : List Bool → D) : Nat → List Bool → D
  | 0, p => lf p
  | h + 1, p => P.inner (sub lf h (p ++ [false])) (sub lf h (p ++ [true]))

/-- `Merkle`: the root and the stored (non-default) nodes. -/
structure St (D : Type) where
  root : D
  nodes : Nat × List Bool → Option D

/-- A node's hash: stored, or the level's default. -/
def getN (nodes : Nat × List Bool → Option D) (l : Nat) (p : List Bool) : D :=
  (nodes (l, p)).getD (dflt P (P.depth - l))

/-- Store a hash; a hash equal to its level's default is removed instead. -/
def storeN (nodes : Nat × List Bool → Option D) (l : Nat) (p : List Bool) (h : D) :
    Nat × List Bool → Option D :=
  if h = dflt P (P.depth - l) then fupd nodes (l, p) none else fupd nodes (l, p) (some h)

theorem getN_storeN (nodes : Nat × List Bool → Option D) (l : Nat) (p : List Bool) (h : D)
    (l' : Nat) (p' : List Bool) :
    getN P (storeN P nodes l p h) l' p' = if (l', p') = (l, p) then h else getN P nodes l' p' := by
  unfold getN storeN
  by_cases hq : (l', p') = (l, p)
  · rw [ite_eq_left hq]
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
    split
    · rename_i hd; rw [fupd_same]; exact hd.symm
    · rw [fupd_same]; rfl
  · rw [ite_eq_right hq]
    split <;> rw [fupd_ne _ _ hq]

/-- The path update of `apply`, from `level` down to the root. -/
def up (a : List Bool) : Nat → (Nat × List Bool → Option D) → D → St D
  | 0, nodes, hash => ⟨hash, storeN P nodes 0 [] hash⟩
  | l + 1, nodes, hash =>
    let nodes1 := storeN P nodes (l + 1) (a.take (l + 1)) hash
    let sib := getN P nodes1 (l + 1) (a.take l ++ [!(a.getD l false)])
    up a l nodes1 (if a.getD l false then P.inner sib hash else P.inner hash sib)

def leafOpt (k : K) : Option (Entry V) → D
  | some e => P.leaf k e
  | none => P.emptyLeaf

/-- The scheme. -/
def scheme : VCImpl K V D where
  S := St D
  empty := fun _ => ⟨dflt P P.depth, fun _ => none⟩
  apply := fun s c => up P (P.addr c.1) P.depth s.nodes (leafOpt P c.1 c.2.2)
  commitment := fun s _ => (s.root, s)

/-- Every stored position holds the recursive subtree hash. -/
def Inv (s : St D) (lf : List Bool → D) : Prop :=
  (∀ l p, l ≤ P.depth → p.length = l → getN P s.nodes l p = sub P lf (P.depth - l) p) ∧
    s.root = sub P lf P.depth []

/-! ## The path update -/

theorem sub_congr (lf lf' : List Bool → D) :
    ∀ (h : Nat) (p : List Bool), (∀ x : List Bool, x.length = h → lf (p ++ x) = lf' (p ++ x)) →
      sub P lf h p = sub P lf' h p
  | 0, p, hx => by simpa [sub] using hx [] rfl
  | h + 1, p, hx => by
    simp only [sub]
    rw [sub_congr lf lf' h (p ++ [false]) (fun x hl => by
          have := hx (false :: x) (by simp [hl]); simpa using this),
        sub_congr lf lf' h (p ++ [true]) (fun x hl => by
          have := hx (true :: x) (by simp [hl]); simpa using this)]

/-- Subtrees off the updated path are unchanged. -/
theorem sub_off_path (lf : List Bool → D) (a : List Bool) (hnew : D) (h : Nat) (p : List Bool)
    (hp : p ≠ a.take p.length) :
    sub P lf h p = sub P (fun x => if x = a then hnew else lf x) h p := by
  apply sub_congr
  intro x _
  have : p ++ x ≠ a := by
    intro he; apply hp; rw [← he]; simp
  simp [this]

theorem sub_const (h : Nat) (p : List Bool) : sub P (fun _ => P.emptyLeaf) h p = dflt P h := by
  induction h generalizing p with
  | zero => rfl
  | succ h ih => simp only [sub, dflt, ih]

theorem take_succ_getD (a : List Bool) (l : Nat) (hl : l < a.length) :
    a.take (l + 1) = a.take l ++ [a.getD l false] := by
  rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  simp

theorem up_spec (a : List Bool) (ha : a.length = P.depth) (lf' : List Bool → D) :
    ∀ (l : Nat) (nodes : Nat × List Bool → Option D) (hash : D), l ≤ P.depth →
      hash = sub P lf' (P.depth - l) (a.take l) →
      (∀ l' p, l' ≤ P.depth → p.length = l' → ¬(l' ≤ l ∧ p = a.take l') →
        getN P nodes l' p = sub P lf' (P.depth - l') p) →
      Inv P (up P a l nodes hash) lf'
  | 0, nodes, hash, _, hh, hn => by
    refine ⟨fun l' p hl' hp => ?_, ?_⟩
    · show getN P (storeN P nodes 0 [] hash) l' p = _
      rw [getN_storeN]
      by_cases hq : (l', p) = (0, [])
      · rw [ite_eq_left hq]; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq; simpa using hh
      · rw [ite_eq_right hq]
        apply hn l' p hl' hp
        rintro ⟨h0, rfl⟩
        have : l' = 0 := Nat.le_zero.1 h0
        subst this
        exact hq (by simp)
    · show hash = _; simpa using hh
  | l + 1, nodes, hash, hl, hh, hn => by
    have hlt : l < a.length := by omega
    let nodes1 := storeN P nodes (l + 1) (a.take (l + 1)) hash
    have hsibne : (l + 1, a.take l ++ [!(a.getD l false)]) ≠ (l + 1, a.take (l + 1)) := by
      rw [take_succ_getD a l hlt]
      intro h
      have := List.append_cancel_left (Prod.mk.inj h).2
      cases hb : a.getD l false <;> simp at this
    have hsib : getN P nodes1 (l + 1) (a.take l ++ [!(a.getD l false)]) =
        sub P lf' (P.depth - (l + 1)) (a.take l ++ [!(a.getD l false)]) := by
      show getN P (storeN P nodes (l + 1) (a.take (l + 1)) hash) _ _ = _
      rw [getN_storeN, ite_eq_right hsibne]
      apply hn _ _ hl (by simp; omega)
      rintro ⟨h1, h2⟩
      apply hsibne
      rw [h2, take_succ_getD a l hlt]
    apply up_spec a ha lf' l nodes1 _ (by omega)
    · have hd : P.depth - l = (P.depth - (l + 1)) + 1 := by omega
      rw [hd]
      simp only [sub]
      show (if a.getD l false = true then P.inner (getN P nodes1 (l + 1) (a.take l ++ [!(a.getD l false)])) hash
        else P.inner hash (getN P nodes1 (l + 1) (a.take l ++ [!(a.getD l false)]))) = _
      rw [hsib]
      have hh' : hash = sub P lf' (P.depth - (l + 1)) (a.take l ++ [a.getD l false]) := by
        rw [hh, take_succ_getD a l hlt]
      rw [hh']
      cases a.getD l false <;> rfl
    · intro l' p hl' hp hnot
      show getN P (storeN P nodes (l + 1) (a.take (l + 1)) hash) l' p = _
      rw [getN_storeN]
      by_cases hq : (l', p) = (l + 1, a.take (l + 1))
      · rw [ite_eq_left hq]; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq; exact hh ▸ rfl
      · rw [ite_eq_right hq]
        apply hn l' p hl' hp
        rintro ⟨h1, h2⟩
        apply hnot
        refine ⟨?_, h2⟩
        by_cases h3 : l' = l + 1
        · subst h3; exact absurd (by rw [h2]) hq
        · omega

/-- **One `apply` call** updates the leaf of its key and keeps the invariant. -/
theorem apply_spec (s : St D) (lf : List Bool → D) (hs : Inv P s lf) (c : Change K V) :
    Inv P ((scheme P).apply s c)
      (fun x => if x = P.addr c.1 then leafOpt P c.1 c.2.2 else lf x) := by
  have ha := P.addr_length c.1
  apply up_spec P (P.addr c.1) ha _ P.depth s.nodes _ (Nat.le_refl _)
  · simp [sub, ← ha]
  · intro l p hl hp hnot
    rw [hs.1 l p hl hp]
    apply sub_off_path
    intro he
    exact hnot ⟨hl, by rw [hp] at he; exact he⟩

/-! ## From sets to leaves -/

/-- The leaf hashes of map `m` over key universe `U`. -/
def lfOf (U : List K) (m : K → Option (Entry V)) (x : List Bool) : D :=
  match U.find? (fun k => decide (P.addr k = x)) with
  | some k => leafOpt P k (m k)
  | none => P.emptyLeaf

theorem lfOf_fupd (hinj : ∀ k₁ k₂, P.addr k₁ = P.addr k₂ → k₁ = k₂) (U : List K)
    (m : K → Option (Entry V)) (k : K) (e : Option (Entry V)) (hk : k ∈ U) (x : List Bool) :
    lfOf P U (fupd m k e) x = if x = P.addr k then leafOpt P k e else lfOf P U m x := by
  unfold lfOf
  by_cases hx : x = P.addr k
  · subst hx
    rw [ite_eq_left rfl]
    have : U.find? (fun k' => decide (P.addr k' = P.addr k)) = some k := by
      apply find?_eq_some_of_unique
      · intro k' _ hk'; exact hinj _ _ (by simpa using hk')
      · exact hk
      · simp
    rw [this]; simp
  · rw [ite_eq_right hx]
    cases hf : U.find? (fun k' => decide (P.addr k' = x)) with
    | none => rfl
    | some k' =>
      have hk' : P.addr k' = x := by simpa using List.find?_some hf
      have : k' ≠ k := fun h => hx (h ▸ hk'.symm)
      simp only
      rw [fupd_ne _ _ this]

theorem lfOf_universe (hinj : ∀ k₁ k₂, P.addr k₁ = P.addr k₂ → k₁ = k₂) (L : List (K × Entry V))
    (U : List K) (hU : ∀ k ∈ keysL L, k ∈ U) : lfOf P U (toMap L) = lfOf P (keysL L) (toMap L) := by
  funext x
  unfold lfOf
  cases h1 : (keysL L).find? (fun k => decide (P.addr k = x)) with
  | some k1 =>
    have hk1 : P.addr k1 = x := by simpa using List.find?_some h1
    have : U.find? (fun k => decide (P.addr k = x)) = some k1 := by
      apply find?_eq_some_of_unique
      · intro k' _ hk'; exact hinj _ _ (by rw [hk1]; simpa using hk')
      · exact hU k1 (List.mem_of_find?_eq_some h1)
      · simp [hk1]
    rw [this]
  | none =>
    cases h2 : U.find? (fun k => decide (P.addr k = x)) with
    | none => rfl
    | some k2 =>
      have hk2 : P.addr k2 = x := by simpa using List.find?_some h2
      have hnot : k2 ∉ keysL L := fun hm => List.find?_eq_none.1 h1 k2 hm (by simp [hk2])
      simp only
      rw [(toMap_eq_none L k2).2 hnot]; rfl

/-- The canonical commitment: the root of the tree over the set's leaves. -/
def F (L : List (K × Entry V)) : D := sub P (lfOf P (keysL L) (toMap L)) P.depth []

theorem fold_spec (hinj : ∀ k₁ k₂, P.addr k₁ = P.addr k₂ → k₁ = k₂) (U : List K) :
    ∀ (calls : List (Change K V)) (s : St D) (m : K → Option (Entry V)),
      (∀ c ∈ calls, c.1 ∈ U) → Inv P s (lfOf P U m) →
      Inv P (calls.foldl (scheme P).apply s) (lfOf P U (calls.foldl (fun f c => fupd f c.1 c.2.2) m))
  | [], _, _, _, hs => hs
  | c :: cs, s, m, hc, hs => by
    show Inv P (cs.foldl (scheme P).apply ((scheme P).apply s c))
      (lfOf P U (cs.foldl (fun f c => fupd f c.1 c.2.2) (fupd m c.1 c.2.2)))
    apply fold_spec hinj U cs _ _ (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc'))
    have := apply_spec P s _ hs c
    have hfun : (fun x => if x = P.addr c.1 then leafOpt P c.1 c.2.2 else lfOf P U m x) =
        lfOf P U (fupd m c.1 c.2.2) := by
      funext x; rw [lfOf_fupd P hinj U m c.1 c.2.2 (hc c (List.mem_cons_self ..))]
    rw [hfun] at this
    exact this

/-- **The sparse Merkle scheme is correct** (no address collisions). -/
theorem smt_correct (o : KeyOrder K) (hinj : ∀ k₁ k₂, P.addr k₁ = P.addr k₂ → k₁ = k₂) :
    (scheme P).Correct o (F P) (fun s L => Inv P s (lfOf P (keysL L) (toMap L))) := by
  refine ⟨fun _ => ⟨fun l p _ _ => ?_, ?_⟩, fun s L L' calls hrep hs hs' hc => ?_⟩
  · show (none : Option D).getD _ = _
    have : lfOf P (keysL ([] : List (K × Entry V))) (toMap []) = fun _ => P.emptyLeaf := by
      funext x; rfl
    rw [this, sub_const]; rfl
  · show dflt P P.depth = _
    have : lfOf P (keysL ([] : List (K × Entry V))) (toMap []) = fun _ => P.emptyLeaf := by
      funext x; rfl
    rw [this, sub_const]
  · let U := keysL L ++ keysL L' ++ calls.map Prod.fst
    have hL : lfOf P U (toMap L) = lfOf P (keysL L) (toMap L) :=
      lfOf_universe P hinj L U (fun k hk => List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hk))))
    have hL' : lfOf P U (toMap L') = lfOf P (keysL L') (toMap L') :=
      lfOf_universe P hinj L' U (fun k hk => List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hk))))
    have h := fold_spec P hinj U calls s (toMap L)
      (fun c hcm => List.mem_append.2 (Or.inr (List.mem_map.2 ⟨c, hcm, rfl⟩))) (by rw [hL]; exact hrep)
    rw [calls_fold_map o _ _ calls hc, hL'] at h
    exact ⟨h.2, h⟩

end SMT
end RightCash
