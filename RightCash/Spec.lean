import RightCash.Engine

/-!
# Specification

This file states what "RightCash is correct" means, independently of how it
is proved. It has three parts:

1. **Reference semantics.** `specPropose` is the consensus meaning of one
   `Propose`: apply the batch to the write set, run the policy's eviction rule
   on its consensus state, and write the victims' final entries to storage on
   top of the parent's view (the *plain path*, design §9.1). `CSys` lifts it
   to the consensus projection of a whole engine (nodes, parents, head).
2. **Root binding** (`RootBinding`, property 1).
3. **Deterministic transitions** (`DeterministicPropose`, property 2) and
   **independence from prefetch hints** (`PrefetchIndependent` and
   `PrefetchIndependentTraces`, property 3), plus the refinement statement
   `Refines` they are derived from.

Throughout, `P` is the eviction policy (with its consensus parameters), `H`
the hash functions, `cap` the consensus capacity: together, "the same
engine". Theorems hold for every choice of them.
-/

set_option linter.unusedSectionVars false

namespace RightCash

variable {K V D : Type} [DecidableEq K]

section Spec
variable (P : Policy K) (H : Hashes K V P.Cons D) (cap : Nat)

/-! ## Reference semantics -/

/-- The consensus meaning of `Propose(batch = b)` on a node in state `st`. -/
def specPropose (st : EState K V P.Cons) (b : List (BatchOp K V)) : EState K V P.Cons :=
  let r := P.specWrites st.policy (b.map BatchOp.key) (st.height + 1) cap
  { height := st.height + 1
    ws := childWS st.ws b r.1
    policy := r.2
    store := fun k => if k ∈ r.1 then (finalEntries st.ws b k).bind Entry.toStore else st.store k }

/-- A node of the consensus projection. -/
structure CNode (K V C D : Type) where
  state : EState K V C
  metaHash : D
  parent : Option Nat

/-- The consensus projection of an engine: what every validator must agree on. -/
structure CSys (K V C D : Type) where
  nodes : Nat → CNode K V C D
  size : Nat
  head : Nat

def CNode.root (n : CNode K V P.Cons D) : D := rootOf H cap n.state n.metaHash

/-- Reference semantics of one labelled action on the consensus projection.
Internal actions (hints, worker activity) do nothing. `none` means the
action is not enabled. -/
def CSys.step [DecidableEq D] (cs : CSys K V P.Cons D) : Label K V → Option (CSys K V P.Cons D)
  | .propose p b md =>
    if p < cs.size then
      some { cs with
        nodes := fupd cs.nodes cs.size ⟨specPropose P cap (cs.nodes p).state b, H.metadata md, some p⟩
        size := cs.size + 1 }
    else none
  | .commit n =>
    if n < cs.size ∧ (cs.nodes n).parent = some cs.head ∧
        (cs.nodes n).root P H cap ≠ (cs.nodes cs.head).root P H cap then
      some { cs with head := n }
    else none
  | .internal => some cs

/-- Run a sequence of actions under the reference semantics. -/
def CSys.run [DecidableEq D] (cs : CSys K V P.Cons D) : List (Label K V) → Option (CSys K V P.Cons D)
  | [] => some cs
  | l :: τ => (cs.step P H cap l).bind (fun cs' => cs'.run τ)

/-- The consensus projection of an engine state: drops prediction marks,
the speculation target and the worker's chain. -/
def Sys.proj (sys : Sys K V D P) : CSys K V P.Cons D :=
  ⟨fun i => ⟨(sys.nodes i).state, (sys.nodes i).metaHash, (sys.nodes i).parent⟩, sys.size, sys.head⟩

/-- The consensus actions of a trace (internal actions removed). -/
def consensusLabels (τ : List (Label K V)) : List (Label K V) := τ.filter (fun l => !l.isInternal)

/-! ## The properties -/

/-- **Property 1 (root binding).** If two instances of the same engine —
with arbitrary, possibly different histories, hints and local settings —
hold nodes with the same root, the nodes have the same consensus state:
the same height, the same buffered write set, the same eviction-policy
state (its eviction order), and the same storage-engine state; unless one
of the hash functions has been broken. -/
def RootBinding [DecidableEq D] : Prop :=
  ∀ sys₁ sys₂ : Sys K V D P, Reachable P H cap sys₁ → Reachable P H cap sys₂ →
    ∀ i j, (sys₁.nodes i).root P H cap = (sys₂.nodes j).root P H cap →
      (sys₁.nodes i).state = (sys₂.nodes j).state ∨ H.Broken

/-- **Property 2 (deterministic transitions).** If two instances hold nodes
with the same root and each proposes the same batch (and metadata) on its
node, the two new nodes have the same consensus state and therefore the
same root; unless a hash has been broken. -/
def DeterministicPropose [DecidableEq D] : Prop :=
  ∀ (sys₁ sys₂ sys₁' sys₂' : Sys K V D P) (p₁ p₂ : Nat) (b : List (BatchOp K V))
    (md : Option (List UInt8)),
    Reachable P H cap sys₁ → Reachable P H cap sys₂ →
    (sys₁.nodes p₁).root P H cap = (sys₂.nodes p₂).root P H cap →
    Step P H cap sys₁ (.propose p₁ b md) sys₁' → Step P H cap sys₂ (.propose p₂ b md) sys₂' →
    ((sys₁'.nodes sys₁.size).state = (sys₂'.nodes sys₂.size).state ∧
      (sys₁'.nodes sys₁.size).root P H cap = (sys₂'.nodes sys₂.size).root P H cap) ∨ H.Broken

/-- **Property 3 (independence from prefetch), functional form.** Whatever
hints the engine received, whatever its worker did or failed to do, and
whether the speculative or the plain path was taken, a `Propose` produces
exactly the reference state `specPropose` of its parent's state. -/
def PrefetchIndependent [DecidableEq D] : Prop :=
  ∀ (sys sys' : Sys K V D P) (p : Nat) (b : List (BatchOp K V)) (md : Option (List UInt8)),
    Reachable P H cap sys → Step P H cap sys (.propose p b md) sys' →
    (sys'.nodes sys.size).state = specPropose P cap (sys.nodes p).state b ∧
      (sys'.nodes sys.size).metaHash = H.metadata md

/-- **Refinement.** The consensus projection of every execution is the
reference run of its consensus actions. -/
def Refines [DecidableEq D] : Prop :=
  ∀ (n0 : Node K V D P) (w : Bool) (τ : List (Label K V)) (sys : Sys K V D P),
    InitOK P n0 → Steps P H cap (Sys.init P n0 w) τ sys →
      CSys.run P H cap ((Sys.init P n0 w).proj P) τ = some (sys.proj P)

/-- **Property 3 (independence from prefetch), two-instance form.** Two
instances that start from the same consensus state and perform the same
consensus actions (`Propose`s and `Commit`s) end in the same consensus
state, no matter how different their prefetch hints, worker timing, worker
failures, speculation settings or prediction marks were. -/
def PrefetchIndependentTraces [DecidableEq D] : Prop :=
  ∀ (n₁ n₂ : Node K V D P) (w₁ w₂ : Bool) (τ₁ τ₂ : List (Label K V)) (sys₁ sys₂ : Sys K V D P),
    InitOK P n₁ → InitOK P n₂ →
    (Sys.init P n₁ w₁).proj P = (Sys.init P n₂ w₂).proj P →
    Steps P H cap (Sys.init P n₁ w₁) τ₁ sys₁ → Steps P H cap (Sys.init P n₂ w₂) τ₂ sys₂ →
    consensusLabels τ₁ = consensusLabels τ₂ →
    sys₁.proj P = sys₂.proj P

end Spec

end RightCash
