import RightCash.Proofs.Invariant

/-!
# The concurrent model: writer, worker thread, channel, readers

The synchronous model (`RightCash.Engine`) applies each worker request when
it is sent. Here the worker is a separate thread:

* the writer sends requests (`Submit`, `Reset`, `Finish`) into a FIFO
  channel (`std::sync::mpsc`) and continues without waiting, except that a
  speculative `Propose` blocks on `Finish`'s reply (`sync_channel(1)`);
* the worker thread, at any moment, dequeues the oldest request, or builds
  (or fails to build) a step from its pending ops;
* hint sources on other threads call `prefetch` through the writer. Since
  `prefetch` takes `&mut self`, their calls are serialised, in any order, with
  every other writer operation; the model lets them arrive in any order and
  at any time the writer is not blocked;
* readers (`Reader`, `Handle`) do not change state; see `RightCash.Concurrent.Proofs`.

A speculative `Propose` is split into `proposeBegin` (apply the batch, send
`Finish`, block) and `proposeEnd` (receive the reply, install the child,
retarget). Between them only the worker, readers and handle drops act.
-/

set_option linter.unusedSectionVars false

namespace RightCash

variable {K V D : Type} [DecidableEq K]

/-- A request on the worker channel (`speculate::Request`). -/
inductive Req (K V : Type) where
  | submit (ops : List (SpecOp K V))
  | reset (base : Store K V)
  | finish (ops : List (SpecOp K V)) (md : Option (List UInt8))

def Req.isFinish {K V : Type} : Req K V → Bool
  | .finish .. => true
  | _ => false

/-- What a request does to the chain, ignoring the reply. -/
def Req.process : Option (Chain K V) → Req K V → Option (Chain K V)
  | c, .submit ops => c.map (·.submit ops)
  | _, .reset base => some (Chain.new base)
  | _, .finish _ _ => none

/-- The chain the worker will have once it has drained the channel (without
building any step): the writer's view of the speculation. -/
def logical (c : Option (Chain K V)) (q : List (Req K V)) : Option (Chain K V) :=
  q.foldl Req.process c

/-- The propose the writer is blocked in. -/
structure Pending (K V : Type) where
  p : Nat
  b : List (BatchOp K V)
  md : Option (List UInt8)

/-- The state of the concurrent system. -/
structure ASys (K V D : Type) (P : Policy K) where
  nodes : Nat → Node K V D P
  size : Nat
  head : Nat
  worker : Bool
  /-- The writer's weak target. -/
  target : Option Nat
  /-- Channel contents, oldest first. -/
  queue : List (Req K V)
  /-- The worker thread's chain (`None` after a `Finish`, until a `Reset`). -/
  chain : Option (Chain K V)
  /-- `Finish`'s reply, once sent. -/
  reply : Option (Option (Store K V))
  /-- The writer is blocked in this `Propose`. -/
  pending : Option (Pending K V)

section Model
variable (P : Policy K) (H : Hashes K V P.Cons D) (cap : Nat)

/-- `retarget`: send `Reset` and the marked entries (no-op without a worker). -/
def ASys.retarget (s : ASys K V D P) (i : Nat) : ASys K V D P :=
  if s.worker then
    { s with target := some i,
             queue := s.queue ++ [.reset (s.nodes i).store,
               .submit (specOps (s.nodes i).ws (P.predicted (s.nodes i).pol) [])] }
  else s

def victimsOf (s : ASys K V D P) (p : Nat) (b : List (BatchOp K V)) : List K :=
  (writesOf P cap (s.nodes p) b).1.victims

/-- A `Propose` that does not wait: the plain path, or a kept chain. -/
def ASys.proposeNow (s : ASys K V D P) (p : Nat) (b : List (BatchOp K V)) (md : Option (List UInt8)) :
    ASys K V D P :=
  let par := s.nodes p
  if s.target = some p then
    { s with nodes := fupd s.nodes s.size (mkChild P H cap par p b md (writesOf P cap par b).2 par.store),
             size := s.size + 1, target := some s.size,
             queue := s.queue ++ [.submit (specOps (childWS par.ws b (writesOf P cap par b).1.victims)
               (writesOf P cap par b).1.evict (writesOf P cap par b).1.retract)] }
  else
    { s with nodes := fupd s.nodes s.size (plainChild P H cap par p b md), size := s.size + 1 }

/-- `finish_speculation`, first half: send `Finish` and block. -/
def ASys.proposeBegin (s : ASys K V D P) (p : Nat) (b : List (BatchOp K V)) (md : Option (List UInt8)) :
    ASys K V D P :=
  let par := s.nodes p
  { s with target := none,
           queue := s.queue ++ [.finish (specOps (finalEntries par.ws b) (writesOf P cap par b).1.evict
             (writesOf P cap par b).1.retract) md],
           pending := some ⟨p, b, md⟩ }

/-- The child built from `Finish`'s reply (`None`: the plain path). -/
def endChild (par : Node K V D P) (p : Nat) (b : List (BatchOp K V)) (md : Option (List UInt8))
    (r : Option (Store K V)) : Node K V D P :=
  match r with
  | some st => mkChild P H cap par p b md (writesOf P cap par b).2 st
  | none => plainChild P H cap par p b md

/-- `finish_speculation`, second half: install the child and retarget to it. -/
def ASys.proposeEnd (s : ASys K V D P) (pp : Pending K V) (r : Option (Store K V)) : ASys K V D P :=
  ASys.retarget P
    { s with nodes := fupd s.nodes s.size (endChild P H cap (s.nodes pp.p) pp.p pp.b pp.md r),
             size := s.size + 1, pending := none, reply := none }
    s.size

def ASys.commit (s : ASys K V D P) (n : Nat) : ASys K V D P :=
  let s1 := { s with head := n }
  if s.worker then
    match s.target with
    | some t => if t = n ∨ (s.nodes t).parent = some n then s1 else s1.retarget P n
    | none => s1.retarget P n
  else s1

def ASys.retargetCond (s : ASys K V D P) (v : Nat) : Bool :=
  match s.target with
  | some t => decide ((s.nodes v).parent = some t)
  | none => decide (v = s.head ∨ (s.nodes v).parent = some s.head)

def ASys.hint (s : ASys K V D P) (v : Nat) (ks : List K) (margin : Nat) : ASys K V D P :=
  if s.target = some v then
    let n := s.nodes v
    let r := P.hintWrites n.pol ks cap margin
    { s with nodes := fupd s.nodes v { n with pol := r.2 },
             queue := s.queue ++ [.submit (specOps n.ws r.1.evict r.1.retract)] }
  else s

def ASys.prefetch (s : ASys K V D P) (v : Nat) (ks : List K) (margin : Nat) : ASys K V D P :=
  if s.worker then
    (if s.retargetCond P v then s.retarget P v else s).hint P cap v ks margin
  else s

/-- The worker thread handles the oldest request. -/
def ASys.dequeue (s : ASys K V D P) (r : Req K V) (q : List (Req K V)) (ok : Bool) : ASys K V D P :=
  match r with
  | .submit ops => { s with queue := q, chain := s.chain.map (·.submit ops) }
  | .reset base => { s with queue := q, chain := some (Chain.new base) }
  | .finish ops md =>
    { s with queue := q, chain := none, reply := some (s.chain.bind (fun c => c.finish ops md ok)) }

/-- One transition of the concurrent system. Writer transitions require that
the writer is not blocked (`pending = none`). -/
inductive AStep [DecidableEq D] : ASys K V D P → Label K V → ASys K V D P → Prop
  | proposeNow (s : ASys K V D P) (p : Nat) (b : List (BatchOp K V)) (md : Option (List UInt8)) :
      s.pending = none → p < s.size →
      ¬(s.target = some p ∧ victimsOf P cap s p b ≠ []) →
      AStep s (.propose p b md) (s.proposeNow P H cap p b md)
  | proposeBegin (s : ASys K V D P) (p : Nat) (b : List (BatchOp K V)) (md : Option (List UInt8)) :
      s.pending = none → p < s.size → s.target = some p → victimsOf P cap s p b ≠ [] →
      AStep s .internal (s.proposeBegin P cap p b md)
  | proposeEnd (s : ASys K V D P) (pp : Pending K V) (r : Option (Store K V)) :
      s.pending = some pp → s.reply = some r →
      AStep s (.propose pp.p pp.b pp.md) (s.proposeEnd P H cap pp r)
  | commit (s : ASys K V D P) (n : Nat) :
      s.pending = none → n < s.size → (s.nodes n).parent = some s.head →
      (s.nodes n).root P H cap ≠ (s.nodes s.head).root P H cap →
      AStep s (.commit n) (s.commit P n)
  | prefetch (s : ASys K V D P) (v : Nat) (ks : List K) (margin : Nat) :
      s.pending = none → v < s.size → AStep s .internal (s.prefetch P cap v ks margin)
  | dropTarget (s : ASys K V D P) : AStep s .internal { s with target := none }
  | dequeue (s : ASys K V D P) (r : Req K V) (q : List (Req K V)) (ok : Bool) :
      s.queue = r :: q → AStep s .internal (s.dequeue P r q ok)
  | build (s : ASys K V D P) (c : Chain K V) (ok : Bool) :
      s.chain = some c → c.failed = false → c.pending ≠ [] →
      AStep s .internal { s with chain := some (if ok then c.build else c.fail) }

inductive ASteps [DecidableEq D] : ASys K V D P → List (Label K V) → ASys K V D P → Prop
  | refl (s : ASys K V D P) : ASteps s [] s
  | cons {s s' s'' : ASys K V D P} {l : Label K V} {τ : List (Label K V)} :
      AStep P H cap s l s' → ASteps s' τ s'' → ASteps s (l :: τ) s''

/-- `RightCash::new`/`recover`; the worker thread starts on the genesis view. -/
def ASys.init (n0 : Node K V D P) (worker : Bool) : ASys K V D P :=
  let g : Node K V D P := { n0 with pol := P.resetHints n0.pol, parent := none }
  { nodes := fun _ => g, size := 1, head := 0, worker,
    target := if worker then some 0 else none, queue := [],
    chain := if worker then some (Chain.new g.store) else none, reply := none, pending := none }

def ASys.proj (s : ASys K V D P) : CSys K V P.Cons D :=
  ⟨fun i => ⟨(s.nodes i).state, (s.nodes i).metaHash, (s.nodes i).parent⟩, s.size, s.head⟩

def AReachable [DecidableEq D] (s : ASys K V D P) : Prop :=
  ∃ (n0 : Node K V D P) (w : Bool) (τ : List (Label K V)), InitOK P n0 ∧ ASteps P H cap (ASys.init P n0 w) τ s

end Model

end RightCash
