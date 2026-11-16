import RightCash.Proofs.Theorems
import RightCash.Policies.Fifo
import RightCash.Policies.Lru
import RightCash.Concurrent.Proofs
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
  semantics `CSys.run`.
-/

set_option linter.unusedSectionVars false

namespace RightCash

variable {K V D : Type} [DecidableEq K] [DecidableEq D]

section FifoResults
variable (le : K → K → Bool) (low cap : Nat) (H : Hashes K V (Fifo.policy le low).Cons D)

theorem fifo_rootBinding : RootBinding (Fifo.policy le low) H cap :=
  rootBinding _ H cap (Fifo.lawful le low)

theorem fifo_deterministicPropose : DeterministicPropose (Fifo.policy le low) H cap :=
  deterministicPropose _ H cap (Fifo.lawful le low)

theorem fifo_prefetchIndependent : PrefetchIndependent (Fifo.policy le low) H cap :=
  prefetchIndependent _ H cap (Fifo.lawful le low)

theorem fifo_prefetchIndependentTraces : PrefetchIndependentTraces (Fifo.policy le low) H cap :=
  prefetchIndependentTraces _ H cap (Fifo.lawful le low)

theorem fifo_refines : Refines (Fifo.policy le low) H cap :=
  refines _ H cap (Fifo.lawful le low)

end FifoResults

section LruResults
variable (le : K → K → Bool) (low cap : Nat) (H : Hashes K V (Lru.policy le low).Cons D)

theorem lru_rootBinding : RootBinding (Lru.policy le low) H cap :=
  rootBinding _ H cap (Lru.lawful le low)

theorem lru_deterministicPropose : DeterministicPropose (Lru.policy le low) H cap :=
  deterministicPropose _ H cap (Lru.lawful le low)

theorem lru_prefetchIndependent : PrefetchIndependent (Lru.policy le low) H cap :=
  prefetchIndependent _ H cap (Lru.lawful le low)

theorem lru_prefetchIndependentTraces : PrefetchIndependentTraces (Lru.policy le low) H cap :=
  prefetchIndependentTraces _ H cap (Lru.lawful le low)

theorem lru_refines : Refines (Lru.policy le low) H cap :=
  refines _ H cap (Lru.lawful le low)

end LruResults

/-! ## Non-vacuity: the hypotheses are satisfiable -/

/-- The empty genesis node `RightCash::new` builds from `Snapshot::empty`. -/
def emptyGenesis (P : Policy K) (pol : P.St) (mh : D) : Node K V D P :=
  ⟨0, emptyMap, pol, emptyMap, mh, none⟩

theorem fifo_initOK_empty (le : K → K → Bool) (low : Nat) (trigger : Option Nat) (mh : D) :
    InitOK (Fifo.policy le low) (emptyGenesis (V := V) (Fifo.policy le low) ⟨[], trigger, [], [], false⟩ mh) :=
  ⟨List.nodup_nil, fun _ => by simp [emptyGenesis, emptyMap, Fifo.policy, Policies.keysOf],
    fun _ => rfl⟩

theorem lru_initOK_empty (le : K → K → Bool) (low : Nat) (trigger : Option Nat) (mh : D) :
    InitOK (Lru.policy le low) (emptyGenesis (V := V) (Lru.policy le low) ⟨[], trigger, [], [], 0, none, 0⟩ mh) :=
  ⟨List.nodup_nil, fun _ => by simp [emptyGenesis, emptyMap, Lru.policy, Policies.keysOf],
    fun _ => rfl⟩

/-- Reachable states exist (with or without speculation). -/
theorem fifo_reachable_init (le : K → K → Bool) (low cap : Nat) (H : Hashes K V (Fifo.policy le low).Cons D)
    (trigger : Option Nat) (mh : D) (w : Bool) :
    Reachable (Fifo.policy le low) H cap
      (Sys.init (Fifo.policy le low) (emptyGenesis (Fifo.policy le low) ⟨[], trigger, [], [], false⟩ mh) w) :=
  ⟨_, w, [], fifo_initOK_empty le low trigger mh, Steps.refl _⟩


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
