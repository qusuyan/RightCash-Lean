import RightCash.Proofs.Theorems
import RightCash.Policies.Fifo
import RightCash.Policies.Lru
import RightCash.Concurrent.Proofs
import RightCash.Proofs.Lookup
import RightCash.Impl.Snapshot
import RightCash.Impl.SparseMerkle
import RightCash.Impl.MerkleBlake3

/-!
# Main results, for the two v0 eviction policies

For FIFO and LRU-write, every key comparison `le`, every low watermark
`low`, every capacity `cap` and every choice of hash functions `H`:

* `*_rootBinding` — **property 1**: equal roots ⇒ equal height, write set,
  eviction order and storage state (or a hash is broken);
* `*_deterministicPropose` — **property 2**: equal roots + same batch ⇒ equal
  next state and equal next root (or a hash is broken);
* `*_prefetchIndependent` and `*_prefetchIndependentTraces` — **property 3**:
  the state after `Propose` does not depend on prefetch hints, worker timing
  or worker failures;
* `*_refines` — the engine's consensus projection follows the reference
  semantics `CSys.run`;
* `*_lookupBinding` — `Revision(root)`, which also resolves an empty-set
  node's storage root (R43), returns nodes that read identically, and have
  the same consensus state when `root` is a combined root (or a hash is
  broken);
* `*_lookupUnique` — under A7 (every batch writes, low watermark ≥ 1),
  every node an engine resolves for one root has the same consensus state.

The initial node may sit on any storage state (R42, `*_initOK_optIn`).
-/

set_option linter.unusedSectionVars false

namespace RightCash

variable {K V D : Type} [DecidableEq K] [DecidableEq D]

section FifoResults
variable (le : K → K → Bool) (low cap : Nat) (H : Hashes K V (Fifo.policy le low).Cons D)

theorem fifo_rootBinding : RootBinding (Fifo.policy le low) H cap :=
  rootBinding _ H cap

theorem fifo_deterministicPropose : DeterministicPropose (Fifo.policy le low) H cap :=
  deterministicPropose _ H cap (Fifo.lawful le low)

theorem fifo_prefetchIndependent : PrefetchIndependent (Fifo.policy le low) H cap :=
  prefetchIndependent _ H cap (Fifo.lawful le low)

theorem fifo_prefetchIndependentTraces : PrefetchIndependentTraces (Fifo.policy le low) H cap :=
  prefetchIndependentTraces _ H cap (Fifo.lawful le low)

theorem fifo_refines : Refines (Fifo.policy le low) H cap :=
  refines _ H cap (Fifo.lawful le low)

theorem fifo_lookupBinding : LookupBinding (Fifo.policy le low) H cap :=
  lookupBinding _ H cap

theorem fifo_lookupUnique (hlow : 1 ≤ low) : LookupUnique (Fifo.policy le low) H cap :=
  lookupUnique _ H cap (Fifo.lawful le low) (Fifo.keepsKey le low hlow)

end FifoResults

section LruResults
variable (le : K → K → Bool) (low cap : Nat) (H : Hashes K V (Lru.policy le low).Cons D)

theorem lru_rootBinding : RootBinding (Lru.policy le low) H cap :=
  rootBinding _ H cap

theorem lru_deterministicPropose : DeterministicPropose (Lru.policy le low) H cap :=
  deterministicPropose _ H cap (Lru.lawful le low)

theorem lru_prefetchIndependent : PrefetchIndependent (Lru.policy le low) H cap :=
  prefetchIndependent _ H cap (Lru.lawful le low)

theorem lru_prefetchIndependentTraces : PrefetchIndependentTraces (Lru.policy le low) H cap :=
  prefetchIndependentTraces _ H cap (Lru.lawful le low)

theorem lru_refines : Refines (Lru.policy le low) H cap :=
  refines _ H cap (Lru.lawful le low)

theorem lru_lookupBinding : LookupBinding (Lru.policy le low) H cap :=
  lookupBinding _ H cap

theorem lru_lookupUnique (hlow : 1 ≤ low) : LookupUnique (Lru.policy le low) H cap :=
  lookupUnique _ H cap (Lru.lawful le low) (Lru.keepsKey le low hlow)

end LruResults

/-! ## Non-vacuity: the hypotheses are satisfiable -/

/-- The initial node `RightCash::new` builds from `Snapshot::empty` in front
of an engine in state `st`: empty, or holding a chain's earlier state (R42). -/
def initNode (P : Policy K) (pol : P.St) (st : Store K V) (mh : D) : Node K V D P :=
  ⟨0, emptyMap, pol, st, mh, none⟩

theorem fifo_initOK_optIn (le : K → K → Bool) (low : Nat) (trigger : Option Nat) (st : Store K V) (mh : D) :
    InitOK (Fifo.policy le low) (initNode (Fifo.policy le low) ⟨[], trigger, [], [], false⟩ st mh) :=
  ⟨List.nodup_nil, fun _ => by simp [initNode, emptyMap, Fifo.policy, Policies.keysOf]⟩

theorem lru_initOK_optIn (le : K → K → Bool) (low : Nat) (trigger : Option Nat) (st : Store K V) (mh : D) :
    InitOK (Lru.policy le low) (initNode (Lru.policy le low) ⟨[], trigger, [], [], 0, none, 0⟩ st mh) :=
  ⟨List.nodup_nil, fun _ => by simp [initNode, emptyMap, Lru.policy, Policies.keysOf]⟩

/-- `validate_policy_keys`, which `new` and `recover` run: the policy's
`index`, which is its order's keys in key order (A4), equals the set's
sorted, distinct keys (`tracks_exactly`). That is exactly `InitOK`. -/
theorem fifo_initOK_of_tracksExactly (le : K → K → Bool) (low : Nat) (n0 : Node K V D (Fifo.policy le low))
    (keys : List K) (hkeys : keys.Nodup) (hset : ∀ k, (n0.ws k).isSome ↔ k ∈ keys)
    (hidx : (Policies.keysOf n0.pol.order).Perm keys) : InitOK (Fifo.policy le low) n0 :=
  ⟨hidx.nodup_iff.2 hkeys, fun k => (hset k).trans hidx.mem_iff.symm⟩

theorem lru_initOK_of_tracksExactly (le : K → K → Bool) (low : Nat) (n0 : Node K V D (Lru.policy le low))
    (keys : List K) (hkeys : keys.Nodup) (hset : ∀ k, (n0.ws k).isSome ↔ k ∈ keys)
    (hidx : (Policies.keysOf n0.pol.order).Perm keys) : InitOK (Lru.policy le low) n0 :=
  ⟨hidx.nodup_iff.2 hkeys, fun k => (hset k).trans hidx.mem_iff.symm⟩

/-- Reachable states exist (with or without speculation), over any storage. -/
theorem fifo_reachable_init (le : K → K → Bool) (low cap : Nat) (H : Hashes K V (Fifo.policy le low).Cons D)
    (trigger : Option Nat) (st : Store K V) (mh : D) (w : Bool) :
    Reachable (Fifo.policy le low) H cap
      (Sys.init (Fifo.policy le low) (initNode (Fifo.policy le low) ⟨[], trigger, [], [], false⟩ st mh) w) :=
  ⟨_, w, [], fifo_initOK_optIn le low trigger st mh, Steps.refl _⟩


/-! ## The concurrent system (worker thread, channel, concurrent hints and readers) -/

section AsyncResults
variable (le : K → K → Bool) (low cap : Nat)

theorem fifo_async_refines (H : Hashes K V (Fifo.policy le low).Cons D) (n0 : Node K V D (Fifo.policy le low))
    (w : Bool) (τ : List (Label K V)) (s : ASys K V D (Fifo.policy le low)) (h0 : InitOK _ n0)
    (hs : ASteps _ H cap (ASys.init _ n0 w) τ s) :
    CSys.run _ H cap ((ASys.init _ n0 w).proj _) τ = some (s.proj _) :=
  async_refines _ H cap (Fifo.lawful le low) n0 w τ s h0 hs

theorem lru_async_refines (H : Hashes K V (Lru.policy le low).Cons D) (n0 : Node K V D (Lru.policy le low))
    (w : Bool) (τ : List (Label K V)) (s : ASys K V D (Lru.policy le low)) (h0 : InitOK _ n0)
    (hs : ASteps _ H cap (ASys.init _ n0 w) τ s) :
    CSys.run _ H cap ((ASys.init _ n0 w).proj _) τ = some (s.proj _) :=
  async_refines _ H cap (Lru.lawful le low) n0 w τ s h0 hs

theorem fifo_async_prefetchIndependentTraces (H : Hashes K V (Fifo.policy le low).Cons D)
    (n₁ n₂ : Node K V D (Fifo.policy le low)) (w₁ w₂ : Bool) (τ₁ τ₂ : List (Label K V))
    (s₁ s₂ : ASys K V D (Fifo.policy le low)) (h₁ : InitOK _ n₁) (h₂ : InitOK _ n₂)
    (hinit : (ASys.init _ n₁ w₁).proj _ = (ASys.init _ n₂ w₂).proj _)
    (hs₁ : ASteps _ H cap (ASys.init _ n₁ w₁) τ₁ s₁) (hs₂ : ASteps _ H cap (ASys.init _ n₂ w₂) τ₂ s₂)
    (hτ : consensusLabels τ₁ = consensusLabels τ₂) : s₁.proj _ = s₂.proj _ :=
  async_prefetchIndependentTraces _ H cap (Fifo.lawful le low) n₁ n₂ w₁ w₂ τ₁ τ₂ s₁ s₂ h₁ h₂ hinit hs₁ hs₂ hτ

theorem lru_async_prefetchIndependentTraces (H : Hashes K V (Lru.policy le low).Cons D)
    (n₁ n₂ : Node K V D (Lru.policy le low)) (w₁ w₂ : Bool) (τ₁ τ₂ : List (Label K V))
    (s₁ s₂ : ASys K V D (Lru.policy le low)) (h₁ : InitOK _ n₁) (h₂ : InitOK _ n₂)
    (hinit : (ASys.init _ n₁ w₁).proj _ = (ASys.init _ n₂ w₂).proj _)
    (hs₁ : ASteps _ H cap (ASys.init _ n₁ w₁) τ₁ s₁) (hs₂ : ASteps _ H cap (ASys.init _ n₂ w₂) τ₂ s₂)
    (hτ : consensusLabels τ₁ = consensusLabels τ₂) : s₁.proj _ = s₂.proj _ :=
  async_prefetchIndependentTraces _ H cap (Lru.lawful le low) n₁ n₂ w₁ w₂ τ₁ τ₂ s₁ s₂ h₁ h₂ hinit hs₁ hs₂ hτ

theorem fifo_async_rootBinding (H : Hashes K V (Fifo.policy le low).Cons D)
    (s₁ s₂ : ASys K V D (Fifo.policy le low)) (h₁ : AReachable _ H cap s₁) (h₂ : AReachable _ H cap s₂)
    (i j : Nat) (h : (s₁.nodes i).root _ H cap = (s₂.nodes j).root _ H cap) :
    (s₁.nodes i).state = (s₂.nodes j).state ∨ H.Broken :=
  async_rootBinding _ H cap (Fifo.lawful le low) s₁ s₂ h₁ h₂ i j h

theorem fifo_async_lookupUnique (H : Hashes K V (Fifo.policy le low).Cons D) (hlow : 1 ≤ low)
    (n0 : Node K V D (Fifo.policy le low)) (w : Bool) (τ : List (Label K V)) (s : ASys K V D (Fifo.policy le low))
    (h0 : InitOK _ n0) (hs : ASteps _ H cap (ASys.init _ n0 w) τ s) (hw : ∀ l ∈ τ, l.Writes)
    (i j : Nat) (r : D) (hi : i < s.size) (hj : j < s.size)
    (h₁ : (s.nodes i).AnswersTo _ H cap r) (h₂ : (s.nodes j).AnswersTo _ H cap r) :
    (s.nodes i).state = (s.nodes j).state ∨ H.Broken :=
  async_lookupUnique _ H cap (Fifo.lawful le low) (Fifo.keepsKey le low hlow) n0 w τ s h0 hs hw i j r hi hj h₁ h₂

theorem lru_async_lookupUnique (H : Hashes K V (Lru.policy le low).Cons D) (hlow : 1 ≤ low)
    (n0 : Node K V D (Lru.policy le low)) (w : Bool) (τ : List (Label K V)) (s : ASys K V D (Lru.policy le low))
    (h0 : InitOK _ n0) (hs : ASteps _ H cap (ASys.init _ n0 w) τ s) (hw : ∀ l ∈ τ, l.Writes)
    (i j : Nat) (r : D) (hi : i < s.size) (hj : j < s.size)
    (h₁ : (s.nodes i).AnswersTo _ H cap r) (h₂ : (s.nodes j).AnswersTo _ H cap r) :
    (s.nodes i).state = (s.nodes j).state ∨ H.Broken :=
  async_lookupUnique _ H cap (Lru.lawful le low) (Lru.keepsKey le low hlow) n0 w τ s h0 hs hw i j r hi hj h₁ h₂

theorem lru_async_rootBinding (H : Hashes K V (Lru.policy le low).Cons D)
    (s₁ s₂ : ASys K V D (Lru.policy le low)) (h₁ : AReachable _ H cap s₁) (h₂ : AReachable _ H cap s₂)
    (i j : Nat) (h : (s₁.nodes i).root _ H cap = (s₂.nodes j).root _ H cap) :
    (s₁.nodes i).state = (s₂.nodes j).state ∨ H.Broken :=
  async_rootBinding _ H cap (Lru.lawful le low) s₁ s₂ h₁ h₂ i j h

end AsyncResults

/-! ## Implementation layer: commitment schemes and the snapshot -/

section ImplResults
variable (o : KeyOrder K)

theorem rehash_ok (Hr : List (K × Entry V) → D) : (rehash Hr).Correct o Hr (fun _ _ => True) :=
  rehash_correct o Hr

theorem lthash_ok {G : Type} (Q : LtParams K V D G) :
    (lthash Q).Correct o (fun L => Q.digest (Q.sumL L)) (fun s L => s = Q.sumL L) :=
  lthash_correct o Q

theorem merkle_ok [DecidableEq D] (Pm : SMT.Params K V D) (hinj : ∀ k₁ k₂, Pm.addr k₁ = Pm.addr k₂ → k₁ = k₂) :
    (SMT.scheme Pm).Correct o (SMT.F Pm) (fun s L => SMT.Inv Pm s (SMT.lfOf Pm (keysL L) (toMap L))) :=
  SMT.smt_correct Pm o hinj

theorem merkleBlake3_ok (Pb : MB3.Params K V D) :
    (MB3.scheme o Pb).Correct o (MB3.F Pb)
      (fun s L => s.changes = [] ∧ ∀ t, s.tree = some t → t = L.map (MB3.leafOf Pb)) :=
  MB3.mb3_correct o Pb

end ImplResults

end RightCash
