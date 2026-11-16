import RightCash.Impl.VC

/-!
# The bottom-up BLAKE3 Merkle scheme (`src/vc/merkle_blake3.rs`)

`apply` only records `(key, in parent, in child)`; `commitment` rebuilds the
tree over the child's entries, copying the parent's leaf hash for every entry
no change touched (`fill_leaves`, which indexes the parent's leaves at
`untouched + replaced`), hashing the others, and then hashing the levels
above. If `fill_leaves` detects inconsistent changes it returns `None` and
the tree is rebuilt from scratch.

The levels above the leaves and the final digest are deterministic functions
of the leaf list (`fill_level`, `digest`); they are abstracted as `topOf` and
`digest`. Batching eight hashes per SIMD lane (`blake3_lanes`) computes the
same keyed hashes and is not modelled.

`fill_spec` shows that every leaf `fill_leaves` produces is the leaf hash of
its entry, so the tree, and hence the digest, is always the full build's.
-/

set_option linter.unusedSectionVars false

namespace RightCash
namespace MB3

structure Params (K V D : Type) where
  /-- The keyed leaf hash of an entry item. -/
  leaf : K → Entry V → D
  /-- The top of the tree over a leaf list (`none` for no leaves). -/
  topOf : List D → Option D
  /-- `digest`: `derive_key` over the leaf count and the top. -/
  digest : Nat → Option D → D

variable {K V D : Type} [DecidableEq K] (o : KeyOrder K) (P : Params K V D)

def leafOf (x : K × Entry V) : D := P.leaf x.1 x.2

/-- The instance: the tree it holds (its leaves) and the recorded changes. -/
structure St (K D : Type) where
  tree : Option (List D)
  changes : List (K × Bool × Bool)

/-- The `while changed < key` loop: skip changes below `k`; each must have
left the child, and counts as replaced if it was in the parent. -/
def skip (k : K) : List (K × Bool × Bool) → Nat → Option (List (K × Bool × Bool) × Nat)
  | [], r => some ([], r)
  | (ck, ip, ic) :: cs, r =>
    if o.lt ck k then (if ic then none else skip k cs (r + ip.toNat))
    else some ((ck, ip, ic) :: cs, r)

/-- After the last entry: remaining changes must have left the child. -/
def tailCount : List (K × Bool × Bool) → Nat → Option Nat
  | [], r => some r
  | (_, ip, ic) :: cs, r => if ic then none else tailCount cs (r + ip.toNat)

/-- `fill_leaves` with a parent tree `Pl` (its leaves), over the child's
entries, the changes, and the counters `untouched`, `replaced`. -/
def fill (Pl : List D) : List (K × Entry V) → List (K × Bool × Bool) → Nat → Nat → Option (List D)
  | [], cs, u, r =>
    match tailCount cs r with
    | some r' => if u + r' = Pl.length then some [] else none
    | none => none
  | (k, e) :: es, cs, u, r =>
    match skip o k cs r with
    | none => none
    | some (cs', r') =>
      match cs' with
      | (ck, ip, ic) :: cs'' =>
        if ck = k then
          (if ic then (fill Pl es cs'' u (r' + ip.toNat)).map (P.leaf k e :: ·) else none)
        else
          match Pl[u + r']? with
          | some h => (fill Pl es cs' (u + 1) r').map (h :: ·)
          | none => none
      | [] =>
        match Pl[u + r']? with
        | some h => (fill Pl es cs' (u + 1) r').map (h :: ·)
        | none => none

/-- `build`'s leaves: reuse when possible, else (genesis, restore, or an
inconsistency) hash every leaf. -/
def buildLeaves (L : List (K × Entry V)) (tree : Option (List D)) (changes : List (K × Bool × Bool)) :
    List D :=
  match tree with
  | none => L.map (leafOf P)
  | some Pl => (fill o P Pl L changes 0 0).getD (L.map (leafOf P))

abbrev scheme : VCImpl K V D where
  S := St K D
  empty := fun _ => ⟨none, []⟩
  apply := fun s c => ⟨s.tree, s.changes ++ [(c.1, c.2.1.isSome, c.2.2.isSome)]⟩
  commitment := fun s L =>
    (P.digest L.length (P.topOf (buildLeaves o P L s.tree s.changes)),
      ⟨some (buildLeaves o P L s.tree s.changes), []⟩)

/-- The canonical commitment: the full build over the set. -/
def F (L : List (K × Entry V)) : D := P.digest L.length (P.topOf (L.map (leafOf P)))

/-! ## Correctness of `fill_leaves` -/

/-- The parent's remaining entries `Lr`, the child's remaining entries `C`
and the remaining changes `cs` describe the same transition. -/
def Aligned (Lr C : List (K × Entry V)) (cs : List (K × Bool × Bool)) : Prop :=
  Sorted o Lr ∧ Sorted o C ∧ cs.Pairwise (fun a b => o.lt a.1 b.1 = true) ∧
  (∀ c ∈ cs, c.2.1 = (toMap Lr c.1).isSome ∧ c.2.2 = (toMap C c.1).isSome) ∧
  (∀ k, toMap Lr k ≠ toMap C k → k ∈ cs.map Prod.fst)

/-- In aligned lists, the parent's first remaining key is not below a key `k`
that is present in it, unless a change below `k` remains. -/
theorem head_key (Lr C : List (K × Entry V)) (cs : List (K × Bool × Bool)) (h : Aligned o Lr C cs)
    (k : K) (hC : ∀ k' ∈ keysL C, o.lt k' k = false)
    (hcs : ∀ c ∈ cs, o.lt c.1 k = false) (hk : k ∈ keysL Lr) :
    ∃ e Lr', Lr = (k, e) :: Lr' := by
  obtain ⟨hsL, _, _, _, hdiff⟩ := h
  cases Lr with
  | nil => simp at hk
  | cons x Lr' =>
    obtain ⟨j, y⟩ := x
    by_cases hj : j = k
    · subst hj; exact ⟨y, Lr', rfl⟩
    · exfalso
      have hjk : o.lt j k = true := by
        simp only [keysL_cons, List.mem_cons] at hk
        rcases hk with h' | h'
        · exact absurd h'.symm hj
        · exact lt_of_sorted_cons o hsL h'
      have hCj : toMap C j = none := (toMap_eq_none C j).2 (fun hm => by
        have := hC j hm; rw [hjk] at this; cases this)
      have hd : toMap ((j, y) :: Lr') j ≠ toMap C j := by rw [toMap_cons, ite_eq_left rfl, hCj]; simp
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 (hdiff j hd)
      have := hcs c hc; rw [hjk] at this; cases this

theorem skip_spec (Pl : List D) (u : Nat) (C : List (K × Entry V)) (k : K)
    (hC : ∀ k' ∈ keysL C, o.lt k' k = false) :
    ∀ (Lr : List (K × Entry V)) (cs : List (K × Bool × Bool)) (r : Nat) (cs' : List (K × Bool × Bool))
      (r' : Nat), Aligned o Lr C cs → Pl.drop (u + r) = Lr.map (leafOf P) →
      skip o k cs r = some (cs', r') →
      ∃ Lr', Aligned o Lr' C cs' ∧ Pl.drop (u + r') = Lr'.map (leafOf P) ∧
        ∀ c ∈ cs', o.lt c.1 k = false
  | Lr, [], r, cs', r', h, hd, hs => by
    simp only [skip, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨Lr, h, hd, by simp⟩
  | Lr, (ck, ip, ic) :: cs, r, cs', r', h, hd, hs => by
    unfold skip at hs
    by_cases hlt : o.lt ck k = true
    · rw [ite_eq_left hlt] at hs
      cases hic : ic
      · rw [hic] at hs
        simp only [Bool.false_eq_true, ite_false] at hs
        obtain ⟨hsL, hsC, hpc, hc, hdiff⟩ := h
        obtain ⟨hlt', hpc'⟩ := List.pairwise_cons.1 hpc
        have hCck : toMap C ck = none := (toMap_eq_none C ck).2 (fun hm => by
          have := hC ck hm; rw [hlt] at this; cases this)
        cases hip : ip
        · -- not in the parent either
          have hLck : toMap Lr ck = none := by
            have := (hc (ck, ip, ic) (List.mem_cons_self ..)).1
            rw [hip] at this
            cases h' : toMap Lr ck
            · rfl
            · rw [h'] at this; cases this
          refine skip_spec Pl u C k hC Lr cs (r + ip.toNat) cs' r' ⟨hsL, hsC, hpc', fun c hcm =>
            hc c (List.mem_cons_of_mem _ hcm), fun k' hk' => ?_⟩ (by rw [hip]; exact hd) hs
          rcases List.mem_cons.1 (hdiff k' hk') with h' | h'
          · subst h'; exact absurd (by rw [hLck, hCck]) hk'
          · exact h'
        · -- the parent's head is `ck`: consume it
          have hin : ck ∈ keysL Lr := by
            have := (hc (ck, ip, ic) (List.mem_cons_self ..)).1
            rw [hip] at this
            exact (toMap_isSome Lr ck).1 this.symm
          obtain ⟨e, Lr', rfl⟩ := head_key o Lr C ((ck, ip, ic) :: cs) ⟨hsL, hsC, hpc, hc, hdiff⟩ ck
            (fun k' hk' => by
              cases hh : o.lt k' ck
              · rfl
              · have := hC k' hk'; rw [o.trans _ _ _ hh hlt] at this; cases this)
            (fun c hcm => by
              rcases List.mem_cons.1 hcm with rfl | hcm
              · exact o.irrefl _
              · exact o.not_lt_of_lt (hlt' c hcm))
            hin
          have hsL' := ((sorted_cons o).1 hsL).2
          refine skip_spec Pl u C k hC Lr' cs (r + ip.toNat) cs' r' ⟨hsL', hsC, hpc', fun c hcm => ?_, fun k' hk' => ?_⟩
            ?_ hs
          · have hcne : c.1 ≠ ck := (o.ne_of_lt (hlt' c hcm)).symm
            have := hc c (List.mem_cons_of_mem _ hcm)
            rw [toMap_cons, ite_eq_right hcne] at this
            exact this
          · by_cases hkk : k' = ck
            · subst hkk
              exfalso; apply hk'
              rw [(toMap_eq_none Lr' k').2 (not_mem_tail_of_sorted o hsL), hCck]
            · have := hdiff k' (by rw [toMap_cons, ite_eq_right hkk]; exact hk')
              rcases List.mem_cons.1 this with h' | h'
              · exact absurd h' hkk
              · exact h'
          · rw [hip]
            show Pl.drop (u + (r + 1)) = _
            rw [← Nat.add_assoc, ← List.drop_drop, hd]
            rfl
      · rw [hic] at hs; simp at hs
    · rw [ite_eq_right hlt] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      refine ⟨Lr, h, hd, fun c hcm => ?_⟩
      rcases List.mem_cons.1 hcm with rfl | hcm
      · simpa using hlt
      · have := (List.pairwise_cons.1 h.2.2.1).1 c hcm
        cases hh : o.lt c.1 k
        · rfl
        · exfalso; exact hlt (o.trans _ _ _ this hh)

/-- Removing key `k` from the parent, the child and the changes keeps them aligned. -/
theorem align_step (Lr Lr2 C C2 : List (K × Entry V)) (cs cs2 : List (K × Bool × Bool)) (k : K)
    (hal : Aligned o Lr C cs) (hs1 : Sorted o Lr2) (hs2 : Sorted o C2)
    (hp2 : cs2.Pairwise (fun a b => o.lt a.1 b.1 = true))
    (hLr : ∀ k', k' ≠ k → toMap Lr2 k' = toMap Lr k') (hLrk : toMap Lr2 k = none)
    (hC : ∀ k', k' ≠ k → toMap C2 k' = toMap C k') (hCk : toMap C2 k = none)
    (hcs : ∀ c ∈ cs2, c ∈ cs ∧ c.1 ≠ k) (hcsB : ∀ c ∈ cs, c.1 ≠ k → c ∈ cs2) :
    Aligned o Lr2 C2 cs2 := by
  obtain ⟨_, _, _, hc, hdiff⟩ := hal
  refine ⟨hs1, hs2, hp2, fun c hcm => ?_, fun k' hk' => ?_⟩
  · obtain ⟨hcm', hne⟩ := hcs c hcm
    rw [hLr _ hne, hC _ hne]; exact hc c hcm'
  · by_cases hkk : k' = k
    · subst hkk; exact absurd (by rw [hLrk, hCk]) hk'
    · rw [hLr _ hkk, hC _ hkk] at hk'
      obtain ⟨c, hcm, rfl⟩ := List.mem_map.1 (hdiff _ hk')
      exact List.mem_map.2 ⟨c, hcsB c hcm hkk, rfl⟩

theorem tail_toMap {k : K} {e : Entry V} {L : List (K × Entry V)} (hs : Sorted o ((k, e) :: L)) :
    (∀ k', k' ≠ k → toMap L k' = toMap ((k, e) :: L) k') ∧ toMap L k = none :=
  ⟨fun k' hk' => by rw [toMap_cons, ite_eq_right hk'], (toMap_eq_none L k).2 (not_mem_tail_of_sorted o hs)⟩

/-- **`fill_leaves` is correct**: if it succeeds, every leaf it returns is
the leaf hash of the corresponding child entry. -/
theorem fill_spec (Pl : List D) : ∀ (C Lr : List (K × Entry V)) (cs : List (K × Bool × Bool))
    (u r : Nat) (ls : List D), Aligned o Lr C cs → Pl.drop (u + r) = Lr.map (leafOf P) →
    fill o P Pl C cs u r = some ls → ls = C.map (leafOf P)
  | [], Lr, cs, u, r, ls, _, _, h => by
    unfold fill at h
    split at h
    · split at h
      · cases h; rfl
      · cases h
    · cases h
  | (k, e) :: es, Lr, cs, u, r, ls, hal, hd, h => by
    have hsC := hal.2.1
    have hC : ∀ k' ∈ keysL ((k, e) :: es), o.lt k' k = false := by
      intro k' hk'
      simp only [keysL_cons, List.mem_cons] at hk'
      rcases hk' with rfl | hk'
      · exact o.irrefl _
      · exact o.not_lt_of_lt (lt_of_sorted_cons o hsC hk')
    obtain ⟨hCt, hCk⟩ := tail_toMap o hsC
    unfold fill at h
    cases hsk : skip o k cs r with
    | none => rw [hsk] at h; cases h
    | some res =>
      obtain ⟨cs', r'⟩ := res
      rw [hsk] at h
      simp only at h
      obtain ⟨Lr', hal', hd', hge⟩ := skip_spec o P Pl u ((k, e) :: es) k hC Lr cs r cs' r' hal hd hsk
      -- the reuse case, shared by "next change is above k" and "no change left"
      have reuse : (∀ c ∈ cs', c.1 ≠ k) →
          (match Pl[u + r']? with
            | some h => (fill o P Pl es cs' (u + 1) r').map (h :: ·)
            | none => none) = some ls → ls = ((k, e) :: es).map (leafOf P) := by
        intro hnk hr
        have hsame : toMap Lr' k = toMap ((k, e) :: es) k := by
          by_cases hdk : toMap Lr' k = toMap ((k, e) :: es) k
          · exact hdk
          · obtain ⟨c, hcm, hck⟩ := List.mem_map.1 (hal'.2.2.2.2 k hdk)
            exact absurd hck (hnk c hcm)
        rw [toMap_cons, ite_eq_left rfl] at hsame
        obtain ⟨e', Lr'', rfl⟩ := head_key o Lr' ((k, e) :: es) cs' hal' k hC hge
          (mem_keysL_of_toMap hsame)
        rw [toMap_cons, ite_eq_left rfl, Option.some.injEq] at hsame
        subst hsame
        have hget : Pl[u + r']? = some (P.leaf k e') := by
          have := congrArg (fun l => l[0]?) hd'
          simp only [List.getElem?_drop, Nat.add_zero] at this
          rw [this]; rfl
        rw [hget] at hr
        simp only [Option.map_eq_some_iff] at hr
        obtain ⟨ls', hls', rfl⟩ := hr
        obtain ⟨hLt, hLk⟩ := tail_toMap o hal'.1
        have halB : Aligned o Lr'' es cs' :=
          align_step o _ _ _ _ _ _ k hal' ((sorted_cons o).1 hal'.1).2 ((sorted_cons o).1 hsC).2
            hal'.2.2.1 hLt hLk hCt hCk (fun c hc => ⟨hc, hnk c hc⟩) (fun c hc _ => hc)
        have hdB : Pl.drop (u + 1 + r') = Lr''.map (leafOf P) := by
          rw [show u + 1 + r' = (u + r') + 1 by omega, ← List.drop_drop, hd']; rfl
        rw [fill_spec Pl es Lr'' cs' (u + 1) r' ls' halB hdB hls']
        rfl
      cases cs' with
      | nil => exact reuse (fun c hc => by cases hc) h
      | cons c0 csT =>
        obtain ⟨ck, ip, ic⟩ := c0
        have hgtT : ∀ c ∈ csT, o.lt ck c.1 = true := (List.pairwise_cons.1 hal'.2.2.1).1
        simp only at h
        by_cases hck : ck = k
        · subst hck
          rw [ite_eq_left rfl] at h
          cases hic : ic
          · rw [hic] at h; cases h
          · rw [hic] at h
            simp only [ite_true, Option.map_eq_some_iff] at h
            obtain ⟨ls', hls', rfl⟩ := h
            have hnk : ∀ c ∈ csT, c.1 ≠ ck := fun c hc => (o.ne_of_lt (hgtT c hc)).symm
            have hcsA : ∀ c ∈ csT, c ∈ (ck, ip, ic) :: csT ∧ c.1 ≠ ck :=
              fun c hc => ⟨List.mem_cons_of_mem _ hc, hnk c hc⟩
            have hcsB : ∀ c ∈ (ck, ip, ic) :: csT, c.1 ≠ ck → c ∈ csT := by
              intro c hc hne
              rcases List.mem_cons.1 hc with rfl | hc
              · exact absurd rfl hne
              · exact hc
            have hpT := (List.pairwise_cons.1 hal'.2.2.1).2
            have hipv := (hal'.2.2.2.1 (ck, ip, ic) (List.mem_cons_self ..)).1
            cases hip : ip
            · -- the key was not in the parent
              have hLk : toMap Lr' ck = none := by
                rw [hip] at hipv
                cases h' : toMap Lr' ck
                · rfl
                · rw [h'] at hipv; cases hipv
              have halB : Aligned o Lr' es csT :=
                align_step o _ _ _ _ _ _ ck hal' hal'.1 ((sorted_cons o).1 hsC).2 hpT
                  (fun _ _ => rfl) hLk hCt hCk hcsA hcsB
              rw [hip] at hls'
              rw [fill_spec Pl es Lr' csT u (r' + false.toNat) ls' halB (by simpa using hd') hls']
              rfl
            · -- the key was in the parent: consume its leaf too
              rw [hip] at hipv
              obtain ⟨e', Lr'', rfl⟩ := head_key o Lr' ((ck, e) :: es) ((ck, ip, ic) :: csT) hal' ck
                hC hge ((toMap_isSome _ _).1 hipv.symm)
              obtain ⟨hLt, hLk⟩ := tail_toMap o hal'.1
              have halB : Aligned o Lr'' es csT :=
                align_step o _ _ _ _ _ _ ck hal' ((sorted_cons o).1 hal'.1).2 ((sorted_cons o).1 hsC).2
                  hpT hLt hLk hCt hCk hcsA hcsB
              have hdB : Pl.drop (u + (r' + true.toNat)) = Lr''.map (leafOf P) := by
                rw [show u + (r' + true.toNat) = (u + r') + 1 by simp; omega, ← List.drop_drop, hd']; rfl
              rw [hip] at hls'
              rw [fill_spec Pl es Lr'' csT u (r' + true.toNat) ls' halB hdB hls']
              rfl
        · rw [ite_eq_right hck] at h
          apply reuse _ h
          intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact hck
          · intro hck'
            have := hge (ck, ip, ic) (List.mem_cons_self ..)
            have hlt := hgtT c hc
            rw [hck'] at hlt
            rw [hlt] at this; cases this

/-! ## The scheme -/

theorem fold_apply (s : St K D) (calls : List (Change K V)) :
    calls.foldl (scheme o P).apply s =
      ⟨s.tree, s.changes ++ calls.map (fun c => (c.1, c.2.1.isSome, c.2.2.isSome))⟩ := by
  induction calls generalizing s with
  | nil => simp
  | cons c cs ih =>
    show List.foldl (scheme o P).apply
      (⟨s.tree, s.changes ++ [(c.1, c.2.1.isSome, c.2.2.isSome)]⟩ : St K D) cs = _
    rw [ih]
    simp [List.append_assoc]

/-- **The merkle-blake3 scheme is correct**: the tree it keeps is always the
full build over the current set, whatever leaves it reused. -/
theorem mb3_correct :
    (scheme o P).Correct o (F P)
      (fun s L => s.changes = [] ∧ ∀ t, s.tree = some t → t = L.map (leafOf P)) := by
  refine ⟨fun _ => ⟨rfl, fun _ h => by cases h⟩, fun s L L' calls hrep hs hs' hc => ?_⟩
  rw [fold_apply, hrep.1, List.nil_append]
  have hleaves : buildLeaves o P L' s.tree (calls.map (fun c => (c.1, c.2.1.isSome, c.2.2.isSome))) =
      L'.map (leafOf P) := by
    unfold buildLeaves
    cases ht : s.tree with
    | none => rfl
    | some Pl =>
      simp only
      cases hf : fill o P Pl L' (calls.map (fun c => (c.1, c.2.1.isSome, c.2.2.isSome))) 0 0 with
      | none => rfl
      | some ls =>
        simp only [Option.getD_some]
        apply fill_spec o P Pl L' L _ 0 0 ls _ (by rw [hrep.2 Pl ht]; rfl) hf
        refine ⟨hs, hs', ?_, fun c hcm => ?_, fun k hk => ?_⟩
        · rw [List.pairwise_map]; exact hc.1
        · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hcm
          obtain ⟨h1, h2⟩ := hc.2.1 c0 hc0
          exact ⟨by rw [h1], by rw [h2]⟩
        · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 (hc.2.2 k hk)
          exact List.mem_map.2 ⟨_, List.mem_map.2 ⟨c0, hc0, rfl⟩, rfl⟩
  refine ⟨?_, rfl, fun t ht => ?_⟩
  · show P.digest L'.length (P.topOf (buildLeaves o P L' s.tree _)) = _
    rw [hleaves]; rfl
  · cases ht; exact hleaves

end MB3
end RightCash
