import RightCash.Basic

/-!
# Hash functions and root composition

Models `src/root.rs` (design §7.3, R42):

```text
root = SHA-256( DOMAIN ‖ static terms ‖ capacity ‖ height
              ‖ set_commitment ‖ policy_digest ‖ storage_root ‖ metadata_hash )
```

at every height, the initial node's included. The initial node may sit on
an engine that already holds state (a chain opting in to right_cash); its
root binds that state through `storage_root`.

## How "with overwhelming probability" is formalised

Hash functions are *uninterpreted* functions. We never assume they are
injective. Instead, every binding statement has the form

> equal roots ⇒ equal states  **∨**  `H.Broken`,

where `H.Broken` says that someone holds an explicit collision of one of the
hash functions, or a *claw*: a combined root equal to a storage root (R43
compares both kinds of root against the same lookup key). The proofs only
ever take apart the preimages they are given, so anyone who finds two states
that falsify the left-hand side has *already found* the collision or claw.
With collision-resistant hashes, and a combined-root hash independent of the
engine's root hash, this happens with negligible probability, which is
exactly the "overwhelming probability" guarantee. This is the standard
reduction-style formalisation and avoids probability theory altogether.

The modelled functions and their Rust counterparts:

| field       | Rust                                                     |
|-------------|----------------------------------------------------------|
| `root`      | `Terms::combine` = SHA-256 ∘ (injective fixed-width encoding of `RootPre`, static terms fixed per engine) |
| `vc`        | `VectorCommitment::commitment` over the retained entries |
| `policy`    | `EvictionPolicy::state_digest` (BLAKE3 over the eviction order) |
| `storage`   | `StorageProposal::root` (`ROOT_IS_STATE_FUNCTION`: a function of the stored state, in the engine's own convention for the empty state) |
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
  root : RootPre D → D
  vc : WriteSet K V → D
  policy : C → D
  storage : Store K V → D
  metadata : Option (List UInt8) → D

/-- `f` has a collision. -/
def Collision {α β : Type} (f : α → β) : Prop := ∃ x y, x ≠ y ∧ f x = f y

/-- Someone holds a collision of one of the hashes, or a claw between the
combined-root hash and the storage-root hash. Negligible-probability event. -/
def Hashes.Broken {K V C D : Type} (H : Hashes K V C D) : Prop :=
  Collision H.root ∨ Collision H.vc ∨ Collision H.policy ∨ Collision H.storage ∨
    ∃ x st, H.root x = H.storage st

/-- If no collision is known, `f` is injective on what we meet. -/
theorem eq_of_not_collision {α β : Type} {f : α → β} (h : ¬Collision f) {x y : α}
    (hxy : f x = f y) : x = y := by
  classical
  by_cases e : x = y
  · exact e
  · exact absurd ⟨x, y, e, hxy⟩ h

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

/-- `Terms::combine`: a node's combined root from its state and metadata hash. -/
def rootOf {K V C D : Type} (H : Hashes K V C D) (cap : Nat) (st : EState K V C) (mh : D) : D :=
  H.root ⟨cap, st.height, H.vc st.ws, H.policy st.policy, H.storage st.store, mh⟩

/-- **Root binding** (state level). Two states with the same root are equal,
unless a hash has been broken. No precondition: since R42 the initial node's
root is a hash like every other node's. -/
theorem rootOf_binding {K V C D : Type} (H : Hashes K V C D) (cap : Nat)
    (st₁ st₂ : EState K V C) (mh₁ mh₂ : D)
    (h : rootOf H cap st₁ mh₁ = rootOf H cap st₂ mh₂) :
    st₁ = st₂ ∨ H.Broken := by
  classical
  by_cases hb : H.Broken
  · exact Or.inr hb
  left
  have nb : ¬Collision H.root ∧ ¬Collision H.vc ∧ ¬Collision H.policy ∧ ¬Collision H.storage :=
    ⟨fun c => hb (Or.inl c), fun c => hb (Or.inr (Or.inl c)), fun c => hb (Or.inr (Or.inr (Or.inl c))),
      fun c => hb (Or.inr (Or.inr (Or.inr (Or.inl c))))⟩
  have hpre := eq_of_not_collision nb.1 h
  injection hpre with _ hh hvc hpol hst _
  have e₁ := eq_of_not_collision nb.2.1 hvc
  have e₂ := eq_of_not_collision nb.2.2.1 hpol
  have e₃ := eq_of_not_collision nb.2.2.2 hst
  cases st₁; cases st₂
  simp_all

/-- Equal roots also bind the metadata hash. -/
theorem rootOf_binding_meta {K V C D : Type} (H : Hashes K V C D) (cap : Nat)
    (st₁ st₂ : EState K V C) (mh₁ mh₂ : D)
    (h : rootOf H cap st₁ mh₁ = rootOf H cap st₂ mh₂) :
    mh₁ = mh₂ ∨ H.Broken := by
  classical
  by_cases hc : Collision H.root
  · exact Or.inr (Or.inl hc)
  have hpre := eq_of_not_collision hc h
  injection hpre with _ _ _ _ _ hm
  exact Or.inl hm

end RightCash
