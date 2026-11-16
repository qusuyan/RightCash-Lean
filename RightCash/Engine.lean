import RightCash.Root
import RightCash.Policy
import RightCash.Worker

/-!
# The engine as a labelled transition system

Models the writer `RightCash` of `src/lib.rs` together with its proposal tree
(`src/proposal.rs`) and its speculation worker (`src/speculate.rs`).

State (`Sys`):
* `nodes` — every node ever created, by id (`nodes i` for `i < size`); a
  node is the immutable record of one proposal (`proposal::Node`), except
  that hints update the prediction marks inside its policy;
* `head` — the committed head (the registry's newest ring entry);
* `worker` — whether speculation is enabled (`Local::speculate`);
* `spec` — the speculation target and the worker's chain (`target` +
  `Worker`), or `none`.

Labels separate **consensus actions** (`propose`, `commit`), which every
validator performs identically, from **internal actions** (`prefetch`
hints, the worker's asynchronous steps and failures, a target node being
dropped), which are local and may differ arbitrarily between validators.

Over-approximations (each only adds behaviours, so every theorem about all
behaviours of the model covers the Rust engine):
* the worker may build or fail a step at any time;
* the final proposal of `finish` may fail;
* `prefetch` may be issued on any live node, with any keys and margin;
* the target may be dropped at any time (its handles released).

Abstracted away (no effect on consensus state): handles and reference
counting, the registry ring and live index (node lookup by root is
`resolve`'s job; we let callers name node ids directly), timings, counters,
`close`, `prune`, checkpointing, and commit failures (which leave the head
unchanged or poison the writer, i.e. only remove behaviours).
-/

set_option linter.unusedSectionVars false

namespace RightCash

variable {K V D : Type} [DecidableEq K]

/-- `proposal::Node`: one proposal. `ws` is the snapshot's records, `pol` its
policy (consensus order plus local marks), `store` the state of its pinned
storage view. -/
structure Node (K V D : Type) (P : Policy K) where
  height : Nat
  ws : WriteSet K V
  pol : P.St
  store : Store K V
  metaHash : D
  parent : Option Nat

/-- The consensus state of a node. -/
def Node.state {P : Policy K} (n : Node K V D P) : EState K V P.Cons :=
  ⟨n.height, n.ws, P.cons n.pol, n.store⟩

/-- The writer's state. -/
structure Sys (K V D : Type) (P : Policy K) where
  nodes : Nat → Node K V D P
  size : Nat
  head : Nat
  worker : Bool
  spec : Option (Nat × Chain K V)

/-- Labels of the transition system. -/
inductive Label (K V : Type) where
  | propose (p : Nat) (b : List (BatchOp K V)) (md : Option (List UInt8))
  | commit (n : Nat)
  | internal

def Label.isInternal {K V : Type} : Label K V → Bool
  | .internal => true
  | _ => false

/-! ## Write-set application (`Snapshot::apply`) -/

/-- Final entry of every key after the batch: the batch wins over the parent
(`merge`: "Equal keys consume both inputs so the batch wins"). -/
def finalEntries (ws : WriteSet K V) (b : List (BatchOp K V)) : WriteSet K V :=
  fun k => (batchFinal b k).or (ws k)

/-- The child's retained records: final entries minus the victims. -/
def childWS (ws : WriteSet K V) (b : List (BatchOp K V)) (victims : List K) : WriteSet K V :=
  fun k => if k ∈ victims then none else finalEntries ws b k

/-- `entries_to_ops(evicted)`: the plain path's storage batch, the victims'
final entries in victim order. -/
def evictedOps (ws : WriteSet K V) (b : List (BatchOp K V)) (victims : List K) :
    List (BatchOp K V) :=
  (victims.filterMap (fun k => (finalEntries ws b k).map (fun e => (k, e)))).map
    (fun ke => BatchOp.ofEntry ke.1 ke.2)

section Engine
variable (P : Policy K) (H : Hashes K V P.Cons D) (cap : Nat)

/-- A node's combined root (`Handle::root`). -/
def Node.root (n : Node K V D P) : D := rootOf H cap n.state n.metaHash

/-- The roots `Registry::lookup` resolves to node `n` (R43): its combined
root, and, while its write set is empty (no entries, no tombstones), its
storage view's root (`Node::bare_root`). -/
def Node.AnswersTo (n : Node K V D P) (r : D) : Prop :=
  n.root P H cap = r ∨ ((∀ k, n.ws k = none) ∧ H.storage n.store = r)

/-- The plain path's storage state for a child of `par` (design §9.1): the
parent's view if nothing is evicted, else the parent's view with every
victim's final entry written. -/
def plainStore (par : Node K V D P) (b : List (BatchOp K V)) (victims : List K) : Store K V :=
  if victims = [] then par.store else applyBatch par.store (evictedOps par.ws b victims)

/-- The chain `retarget` starts on node `n`: a `Reset` to its view, then its
still-marked entries (`spec_ops(snapshot, predicted, ∅)`). -/
def retargetChain (n : Node K V D P) : Chain K V :=
  (Chain.new n.store).submit (specOps n.ws (P.predicted n.pol) [])

def retargetSpec (worker : Bool) (i : Nat) (n : Node K V D P) : Option (Nat × Chain K V) :=
  if worker then some (i, retargetChain P n) else none

/-- `RightCash::retarget` (a no-op without a worker). -/
def Sys.retarget (sys : Sys K V D P) (i : Nat) : Sys K V D P :=
  { sys with spec := retargetSpec P sys.worker i (sys.nodes i) }

/-- `Snapshot::apply`'s policy call: the parent's policy is cloned, marks
included, and runs `writes` on the batch's keys at the child's height. -/
def writesOf (par : Node K V D P) (b : List (BatchOp K V)) : Eviction K × P.St :=
  P.writes par.pol (b.map BatchOp.key) (par.height + 1) cap

/-- The child node of `par` (id `p`) with policy `pol` and storage state `st`. -/
def mkChild (par : Node K V D P) (p : Nat) (b : List (BatchOp K V)) (md : Option (List UInt8))
    (pol : P.St) (st : Store K V) : Node K V D P :=
  ⟨par.height + 1, childWS par.ws b (writesOf P cap par b).1.victims, pol, st, H.metadata md, some p⟩

/-- The plain path (design §9.1): marks cleared (`snapshot.reset_hints()`),
storage built on the parent's view. -/
def plainChild (par : Node K V D P) (p : Nat) (b : List (BatchOp K V)) (md : Option (List UInt8)) :
    Node K V D P :=
  mkChild P H cap par p b md (P.resetHints (writesOf P cap par b).2)
    (plainStore P par b (writesOf P cap par b).1.victims)

/-- `finish_speculation`: the final ops carry the victims' final entries; on
success the child takes the worker's view, on failure the plain path. -/
def finishChild (par : Node K V D P) (p : Nat) (b : List (BatchOp K V)) (md : Option (List UInt8))
    (c : Chain K V) (ok : Bool) : Node K V D P :=
  match c.finish (specOps (finalEntries par.ws b) (writesOf P cap par b).1.evict
      (writesOf P cap par b).1.retract) md ok with
  | some st => mkChild P H cap par p b md (writesOf P cap par b).2 st
  | none => plainChild P H cap par p b md

/-- `RightCash::propose(parent = p, batch = b, metadata = md)`: the new node
and the new speculation state. `ok` resolves the nondeterminism of the
worker's final build. -/
def proposeOut (sys : Sys K V D P) (p : Nat) (b : List (BatchOp K V)) (md : Option (List UInt8))
    (ok : Bool) : Node K V D P × Option (Nat × Chain K V) :=
  let par := sys.nodes p
  match sys.spec with
  | some (t, c) =>
    if t = p then
      if (writesOf P cap par b).1.victims = [] then
        -- Keep the chain (R35): inherit the parent's view; `block_end` the
        -- refinement; the child becomes the target.
        (mkChild P H cap par p b md (writesOf P cap par b).2 par.store,
          some (sys.size, c.submit (specOps (childWS par.ws b (writesOf P cap par b).1.victims)
            (writesOf P cap par b).1.evict (writesOf P cap par b).1.retract)))
      else
        -- Finalize; the chain is consumed; retarget to the completed child.
        (finishChild P H cap par p b md c ok,
          retargetSpec P sys.worker sys.size (finishChild P H cap par p b md c ok))
    else (plainChild P H cap par p b md, sys.spec)
  | none => (plainChild P H cap par p b md, sys.spec)

def Sys.propose (sys : Sys K V D P) (p : Nat) (b : List (BatchOp K V)) (md : Option (List UInt8))
    (ok : Bool) : Sys K V D P :=
  { sys with
    nodes := fupd sys.nodes sys.size (proposeOut P H cap sys p b md ok).1
    size := sys.size + 1
    spec := (proposeOut P H cap sys p b md ok).2 }

/-- `RightCash::commit(n)` after its checks succeed, followed by
`after_commit`. The storage commit does not change any view's state. -/
def Sys.commit (sys : Sys K V D P) (n : Nat) : Sys K V D P :=
  let sys1 := { sys with head := n }
  if sys.worker then
    match sys.spec with
    | some (t, _) =>
      if t = n ∨ (sys.nodes t).parent = some n then sys1 else sys1.retarget P n
    | none => sys1.retarget P n
  else sys1

/-- `prefetch`'s retarget rule. -/
def retargetCond (sys : Sys K V D P) (v : Nat) : Bool :=
  match sys.spec with
  | some (t, _) => decide ((sys.nodes v).parent = some t)
  | none => decide (v = sys.head ∨ (sys.nodes v).parent = some sys.head)

/-- A hint on node `v`, if it is the target: `hint_writes` updates its marks
and the resulting ops are submitted to the worker. -/
def Sys.hint (sys : Sys K V D P) (v : Nat) (ks : List K) (margin : Nat) : Sys K V D P :=
  match sys.spec with
  | some (t, c) =>
    if t = v then
      let n := sys.nodes v
      let r := P.hintWrites n.pol ks cap margin
      { sys with
        nodes := fupd sys.nodes v { n with pol := r.2 }
        spec := some (t, c.submit (specOps n.ws r.1.evict r.1.retract)) }
    else sys
  | none => sys

/-- `RightCash::prefetch(view = v, keys = ks)` with speculation margin `margin`. -/
def Sys.prefetch (sys : Sys K V D P) (v : Nat) (ks : List K) (margin : Nat) : Sys K V D P :=
  if sys.worker then
    let sys1 := if retargetCond P sys v then sys.retarget P v else sys
    sys1.hint P cap v ks margin
  else sys

/-- The worker builds a step from its pending ops (`ok`), or the step fails. -/
def Sys.workerStep (sys : Sys K V D P) (ok : Bool) : Sys K V D P :=
  match sys.spec with
  | some (t, c) =>
    if c.failed = false ∧ c.pending ≠ [] then
      { sys with spec := some (t, if ok then c.build else c.fail) }
    else sys
  | none => sys

/-- One transition. -/
inductive Step [DecidableEq D] : Sys K V D P → Label K V → Sys K V D P → Prop
  | propose (sys : Sys K V D P) (p : Nat) (b : List (BatchOp K V)) (md : Option (List UInt8))
      (ok : Bool) :
      p < sys.size → Step sys (.propose p b md) (sys.propose P H cap p b md ok)
  /-- `commit` checks: the node is not the head's root (`ProposalConsumed`),
  its parent is the head (`ParentUncommitted`/`ProposalOrphaned`). -/
  | commit (sys : Sys K V D P) (n : Nat) :
      n < sys.size → (sys.nodes n).parent = some sys.head →
      (sys.nodes n).root P H cap ≠ (sys.nodes sys.head).root P H cap →
      Step sys (.commit n) (sys.commit P n)
  | prefetch (sys : Sys K V D P) (v : Nat) (ks : List K) (margin : Nat) :
      v < sys.size → Step sys .internal (sys.prefetch P cap v ks margin)
  | worker (sys : Sys K V D P) (ok : Bool) : Step sys .internal (sys.workerStep P ok)
  | dropTarget (sys : Sys K V D P) : Step sys .internal { sys with spec := none }

/-- Finite executions, recording their labels. -/
inductive Steps [DecidableEq D] : Sys K V D P → List (Label K V) → Sys K V D P → Prop
  | refl (sys : Sys K V D P) : Steps sys [] sys
  | cons {s s' s'' : Sys K V D P} {l : Label K V} {τ : List (Label K V)} :
      Step P H cap s l s' → Steps s' τ s'' → Steps s (l :: τ) s''

/-- `RightCash::new`/`recover` on initial node `n0`: marks are reset; with
speculation on, the initial node is the target and the worker starts on
its view. Unused slots of `nodes` hold the initial node too. The initial
node's height, write set and storage are arbitrary (R42: `new` accepts an
engine that already holds state, and `recover` any checkpoint). -/
def Sys.init (n0 : Node K V D P) (worker : Bool) : Sys K V D P :=
  let g : Node K V D P := { n0 with pol := P.resetHints n0.pol, parent := none }
  { nodes := fun _ => g, size := 1, head := 0, worker,
    spec := if worker then some (0, Chain.new g.store) else none }

/-- Preconditions on the initial node: the policy tracks exactly the set's
keys, without duplicates. `new` and `recover` check it
(`Snapshot::validate_policy_keys`; see `fifo_initOK_of_tracksExactly`).
Nothing constrains the storage state or the height. -/
def InitOK (n0 : Node K V D P) : Prop :=
  P.wf (P.cons n0.pol) ∧ (∀ k, (n0.ws k).isSome ↔ k ∈ P.tracked (P.cons n0.pol))

/-- States reachable from some valid initial node, with or without
speculation, by any finite execution. -/
def Reachable [DecidableEq D] (sys : Sys K V D P) : Prop :=
  ∃ (n0 : Node K V D P) (w : Bool) (τ : List (Label K V)),
    InitOK P n0 ∧ Steps P H cap (Sys.init P n0 w) τ sys

end Engine

end RightCash
