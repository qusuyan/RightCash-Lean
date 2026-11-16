import RightCash.Basic

/-!
# Eviction-policy interface

Models the `EvictionPolicy` trait (`src/policy/mod.rs`, design §6.1). A
policy value in Rust carries two kinds of state:

* **consensus state** (the eviction order) — covered by `state_digest`, a
  root term; and
* **local prediction state** (`marked`, hint bookkeeping) — written by
  prefetch hints, never hashed, and allowed to differ between validators.

`Policy` packages one concrete policy: its full state type `St` (the Rust
struct), the consensus projection `cons`, the reference consensus semantics
`specWrites`, and the Rust entry points `writes`, `hint_writes`,
`reset_hints`, `predicted`. `Policy.Lawful` lists the facts about a policy
that the engine-level proofs use; `RightCash.Fifo` and `RightCash.Lru`
prove them for the two v0 policies from their concrete code.
-/

namespace RightCash

/-- `policy::Eviction`, flattened: `victims` is `all_evicted_keys`;
`evict`/`retract` are `refinement.evict`/`refinement.retract`. -/
structure Eviction (K : Type) where
  victims : List K
  evict : List K
  retract : List K

/-- `policy::Prediction`. -/
structure Prediction (K : Type) where
  evict : List K
  retract : List K

/-- The storage operations `(E, R)` returned with a mark change `m → m'`
describe that change exactly. The writer turns them into worker ops with
`spec_ops`: all `Evict`s first, then all `Retract`s, and the worker's pending
map keeps the last op per key. So for each key: a retraction wins and must
leave the key unmarked; otherwise an eviction must leave it marked;
otherwise the mark must not change. -/
def MarkDelta {K : Type} (m m' E R : List K) : Prop :=
  ∀ k, (k ∈ R → k ∉ m') ∧ (k ∉ R → k ∈ E → k ∈ m') ∧ (k ∉ R → k ∉ E → (k ∈ m' ↔ k ∈ m))

/-- What the final refinement of an evicting block must satisfy, relative to
the marks `m` before the block and the batch's written keys `ks`
(design §9.1):
1. it only evicts actual victims (Rust: `expect("final refinement must name
   an actual victim")`);
2. a victim it omits was predicted and not rewritten, so the chain already
   holds its final entry;
3. every retained prediction is retracted;
4. it never retracts a victim. -/
def FinalOK {K : Type} (m ks : List K) (ev : Eviction K) : Prop :=
  (∀ k ∈ ev.evict, k ∈ ev.victims) ∧
  (∀ k ∈ ev.victims, k ∉ ev.evict → k ∈ m ∧ k ∉ ks) ∧
  (∀ k ∈ m, k ∉ ev.victims → k ∈ ev.retract) ∧
  (∀ k ∈ ev.retract, k ∉ ev.victims)

/-- One eviction policy (an `EvictionPolicy` implementation together with
its consensus parameters, e.g. the low watermark). -/
structure Policy (K : Type) where
  /-- The full Rust policy struct (consensus and local fields). -/
  St : Type
  /-- The consensus state (what `state_digest` covers). -/
  Cons : Type
  cons : St → Cons
  /-- Keys tracked by the consensus state (= the write set's keys). -/
  tracked : Cons → List K
  /-- Structural well-formedness of a consensus state (no duplicate keys). -/
  wf : Cons → Prop
  /-- The local prediction marks (`marked`). -/
  marked : St → List K
  /-- Consensus state of a freshly constructed policy. -/
  fresh : Cons
  /-- Reference consensus semantics of `writes`: written keys, height, capacity
  ↦ victims and next consensus state. -/
  specWrites : Cons → List K → Nat → Nat → List K × Cons
  /-- `EvictionPolicy::writes(keys, height, capacity)`. -/
  writes : St → List K → Nat → Nat → Eviction K × St
  /-- `EvictionPolicy::hint_writes(keys, capacity, margin)`. -/
  hintWrites : St → List K → Nat → Nat → Prediction K × St
  /-- `EvictionPolicy::reset_hints`. -/
  resetHints : St → St
  /-- `EvictionPolicy::predicted`. -/
  predicted : St → List K

/-- The properties of a policy that the engine proofs rely on. -/
structure Policy.Lawful {K : Type} (P : Policy K) : Prop where
  /-- Actual victims are a function of the consensus state alone (marks never
  influence eviction, design §6.1). -/
  writes_victims : ∀ s ks h cap,
    (P.writes s ks h cap).1.victims = (P.specWrites (P.cons s) ks h cap).1
  /-- So is the next consensus state. -/
  writes_cons : ∀ s ks h cap,
    P.cons (P.writes s ks h cap).2 = (P.specWrites (P.cons s) ks h cap).2
  /-- Hints never change consensus state. -/
  hint_cons : ∀ s ks cap margin, P.cons (P.hintWrites s ks cap margin).2 = P.cons s
  reset_cons : ∀ s, P.cons (P.resetHints s) = P.cons s
  reset_marked : ∀ s, P.marked (P.resetHints s) = []
  predicted_eq : ∀ s, P.predicted s = P.marked s
  wf_fresh : P.wf P.fresh
  fresh_tracked : P.tracked P.fresh = []
  wf_writes : ∀ c ks h cap, P.wf c → P.wf (P.specWrites c ks h cap).2
  /-- Tracked keys after a batch: old or written, minus the victims. -/
  tracked_writes : ∀ c ks h cap k, P.wf c →
    (k ∈ P.tracked (P.specWrites c ks h cap).2 ↔
      (k ∈ P.tracked c ∨ k ∈ ks) ∧ k ∉ (P.specWrites c ks h cap).1)
  /-- Victims exist in the parent or the batch (`merge`'s `unreachable!`). -/
  victims_sub : ∀ c ks h cap k, k ∈ (P.specWrites c ks h cap).1 → k ∈ P.tracked c ∨ k ∈ ks
  /-- Marks stay within the tracked keys. -/
  writes_marked : ∀ s ks h cap, P.wf (P.cons s) → (∀ k ∈ P.marked s, k ∈ P.tracked (P.cons s)) →
    ∀ k ∈ P.marked (P.writes s ks h cap).2, k ∈ P.tracked (P.cons (P.writes s ks h cap).2)
  hint_marked : ∀ s ks cap margin, (∀ k ∈ P.marked s, k ∈ P.tracked (P.cons s)) →
    ∀ k ∈ P.marked (P.hintWrites s ks cap margin).2, k ∈ P.tracked (P.cons s)
  /-- A hint's storage ops describe its mark change. -/
  hint_delta : ∀ s ks cap margin,
    MarkDelta (P.marked s) (P.marked (P.hintWrites s ks cap margin).2)
      (P.hintWrites s ks cap margin).1.evict (P.hintWrites s ks cap margin).1.retract
  /-- A non-evicting block's refinement describes its mark change, and a
  rewritten key that stays marked is resent. -/
  kept_delta : ∀ s ks h cap, (P.writes s ks h cap).1.victims = [] →
    MarkDelta (P.marked s) (P.marked (P.writes s ks h cap).2)
      (P.writes s ks h cap).1.evict (P.writes s ks h cap).1.retract ∧
    ∀ k ∈ ks, k ∈ P.marked (P.writes s ks h cap).2 → k ∈ (P.writes s ks h cap).1.evict
  /-- An evicting block's final refinement reconciles the marks with the victims. -/
  final : ∀ s ks h cap, (P.writes s ks h cap).1.victims ≠ [] →
    FinalOK (P.marked s) ks (P.writes s ks h cap).1

end RightCash
