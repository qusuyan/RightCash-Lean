import RightCash.Basic

/-!
# Hash functions and root composition

Models `src/root.rs` (design §7.3):

```text
root = EMPTY_ROOT                                       if height == 0
     = SHA-256( DOMAIN ‖ static terms ‖ capacity ‖ height
              ‖ set_commitment ‖ policy_digest ‖ storage_root ‖ metadata_hash )
```

## How "with overwhelming probability" is formalised

Hash functions are *uninterpreted* functions. We never assume they are
injective. Instead, every binding statement has the form

> equal roots ⇒ equal states  **∨**  `H.Broken`,

where `H.Broken` says that someone holds an explicit collision of one of the
hash functions (or a preimage of the `EMPTY_ROOT` constant under the root
hash). The proofs only ever take apart the two preimages they are given, so
anyone who finds two states that falsify the left-hand side has *already
found* the collision. With collision-resistant (and preimage-resistant)
hashes this happens with negligible probability, which is exactly the
"overwhelming probability" guarantee. This is the standard reduction-style
formalisation and avoids probability theory altogether.

The modelled functions and their Rust counterparts:

| field       | Rust                                                     |
|-------------|----------------------------------------------------------|
| `root`      | `Terms::combine` = SHA-256 ∘ (injective fixed-width encoding of `RootPre`, static terms fixed per engine) |
| `vc`        | `VectorCommitment::commitment` over the retained entries |
| `policy`    | `EvictionPolicy::state_digest` (BLAKE3 over the eviction order) |
| `storage`   | `StorageProposal::root` (`ROOT_IS_STATE_FUNCTION`: a function of the stored state) |
| `metadata`  | `root::metadata_hash`                                     |

The static terms (`DOMAIN`, scheme/policy/engine identifiers and parameter
digests) are identical for two instances of the same engine, so they are
folded into `root`. Every field of `RootPre` is fixed-width in the encoding
(capacity and height as `u64 LE`, 32-byte digests), hence the encoding is
injective and a collision of `root` is a SHA-256 collision.
-/

namespace RightCash

/-- The node-dependent part of the root preimage. -/
structure RootPre (D : Type) where
  capacity : Nat
  height : Nat
  setCommitment : D
  policyDigest : D
  storageRoot : D
  metadataHash : D

/-- The hash functions of one engine configuration. `C` is the policy's
consensus-state type, `D` the 32-byte digest type. -/
structure Hashes (K V C D : Type) where
  emptyRoot : D
  root : RootPre D → D
  vc : WriteSet K V → D
  policy : C → D
  storage : Store K V → D
  metadata : Option (List UInt8) → D

/-- `f` has a collision. -/
def Collision {α β : Type} (f : α → β) : Prop := ∃ x y, x ≠ y ∧ f x = f y

/-- Someone holds a collision of one of the hashes, or a preimage of
`EMPTY_ROOT` under the root hash. Negligible-probability event. -/
def Hashes.Broken {K V C D : Type} (H : Hashes K V C D) : Prop :=
  Collision H.root ∨ Collision H.vc ∨ Collision H.policy ∨ Collision H.storage ∨
    ∃ x, H.root x = H.emptyRoot

/-- The consensus state of one node, i.e. everything a root must bind:
height, the buffered write set (tombstones included), the eviction policy's
consensus state, and the storage engine's state behind the node's pinned
view. Local, non-consensus state (prediction marks, the speculation worker)
is deliberately *not* part of it. -/
structure EState (K V C : Type) where
  height : Nat
  ws : WriteSet K V
  policy : C
  store : Store K V

/-- The height-0 initial state: an empty set, a fresh policy, fresh storage. -/
def EState.empty {K V C : Type} (fresh : C) : EState K V C :=
  ⟨0, emptyMap, fresh, emptyMap⟩

/-- `Terms::combine`: a node's combined root from its state and metadata hash. -/
def rootOf {K V C D : Type} (H : Hashes K V C D) (cap : Nat) (st : EState K V C) (mh : D) : D :=
  if st.height = 0 then H.emptyRoot
  else H.root ⟨cap, st.height, H.vc st.ws, H.policy st.policy, H.storage st.store, mh⟩

/-- The genesis convention: a height-0 state is the empty initial state
(`RightCash::new` requires fresh storage; `Snapshot::empty` requires a fresh
policy). -/
def GenesisOK {K V C : Type} (fresh : C) (st : EState K V C) : Prop :=
  st.height = 0 → st = EState.empty fresh

/-- **Root binding** (state level). Two states with the same root are equal,
unless a hash has been broken. -/
theorem rootOf_binding {K V C D : Type} (H : Hashes K V C D) (cap : Nat) (fresh : C)
    (st₁ st₂ : EState K V C) (mh₁ mh₂ : D)
    (g₁ : GenesisOK fresh st₁) (g₂ : GenesisOK fresh st₂)
    (h : rootOf H cap st₁ mh₁ = rootOf H cap st₂ mh₂) :
    st₁ = st₂ ∨ H.Broken := by
  unfold rootOf at h
  by_cases h₁ : st₁.height = 0 <;> by_cases h₂ : st₂.height = 0
  · exact Or.inl ((g₁ h₁).trans (g₂ h₂).symm)
  · simp only [h₁, h₂, ite_true, ite_false] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, h.symm⟩))))
  · simp only [h₁, h₂, ite_true, ite_false] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, h⟩))))
  · simp only [h₁, h₂, ite_false] at h
    classical
    by_cases hpre : (⟨cap, st₁.height, H.vc st₁.ws, H.policy st₁.policy, H.storage st₁.store, mh₁⟩ :
        RootPre D) = ⟨cap, st₂.height, H.vc st₂.ws, H.policy st₂.policy, H.storage st₂.store, mh₂⟩
    · injection hpre with _ hh hvc hpol hst _
      by_cases e₁ : st₁.ws = st₂.ws
      · by_cases e₂ : st₁.policy = st₂.policy
        · by_cases e₃ : st₁.store = st₂.store
          · left
            cases st₁; cases st₂
            simp_all
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, e₃, hst⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, e₂, hpol⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨_, _, e₁, hvc⟩))
    · exact Or.inr (Or.inl ⟨_, _, hpre, h⟩)

/-- Equal non-genesis roots also bind the metadata hash. -/
theorem rootOf_binding_meta {K V C D : Type} (H : Hashes K V C D) (cap : Nat)
    (st₁ st₂ : EState K V C) (mh₁ mh₂ : D) (hne : st₁.height ≠ 0)
    (h : rootOf H cap st₁ mh₁ = rootOf H cap st₂ mh₂) :
    mh₁ = mh₂ ∨ H.Broken := by
  classical
  unfold rootOf at h
  by_cases h₂ : st₂.height = 0
  · simp only [hne, h₂, ite_true, ite_false] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, h⟩))))
  · simp only [hne, h₂, ite_false] at h
    by_cases hpre : (⟨cap, st₁.height, H.vc st₁.ws, H.policy st₁.policy, H.storage st₁.store, mh₁⟩ :
        RootPre D) = ⟨cap, st₂.height, H.vc st₂.ws, H.policy st₂.policy, H.storage st₂.store, mh₂⟩
    · injection hpre with _ _ _ _ _ hm
      exact Or.inl hm
    · exact Or.inr (Or.inl ⟨_, _, hpre, h⟩)

end RightCash
