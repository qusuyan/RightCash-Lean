# RightCash correctness: specification and proof status

This document states what it means for the RightCash storage engine
(the `rust/` submodule, commit `ce7dba2`) to be correct, which model of the code the
statements are about, and what the Lean development in this repository proves.
Every statement below has a Lean counterpart; the names are given in
`monospace` and live in the `RightCash` namespace.

**Status.** Everything below is proved, with no `sorry`. The main theorems
depend only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); `scripts/Audit.lean` prints them.

* **Engine properties 1–3, and refinement**, for both v0 eviction policies
  (FIFO, LRU-write), every capacity, low watermark, key order and choice of
  hash functions (§5). They hold for the synchronous model (§1) and for the
  concurrent model with a separate worker thread (§8).
* **Commitment schemes**: `rehash`, `lthash`, the sparse Merkle tree and
  `merkle-blake3` each keep a commitment that is a function of the set alone
  (§7.2).
* **Snapshot and arena**: `merge`, `normalise` and `compact` implement the
  abstract write-set update; every slot of a live snapshot reads inside its
  own arena, so no referenced chunk is ever freed (§7.1, §7.3).
* **Readers**: a node's read-visible data never changes after it is created,
  and eviction is invisible to reads (§8.3).

How the proofs are pinned to the Rust code and kept in sync with it is
described in §10.

---

## 1. What is modelled, and what is trusted

### 1.1 In the model

| Rust (`rust/src`) | Lean | Notes |
|---|---|---|
| `set::Snapshot::apply`, `normalise`, `merge` | `batchFinal`, `finalEntries`, `childWS`, `evictedOps` (`Basic`, `Engine`) | Write set as a finite map `K → Option (Entry V)`; tombstones kept. |
| `policy::EvictionPolicy` | `Policy`, `Policy.Lawful` (`Policy`) | Abstract interface plus the laws the proofs need. |
| `policy::fifo::Fifo` | `Fifo.St`, `Fifo.writes`, `Fifo.hintWrites`, … (`Policies/Fifo`) | Transcribed function by function, with prediction marks. |
| `policy::lru_write::LruWrite` | `Lru.St`, `Lru.writes`, `Lru.hintWrites`, `Lru.fill`, … (`Policies/Lru`) | Same, including the candidate cursor loop. |
| `speculate::{Chain, SpecOp, run, build_step, put_back}` | `Chain`, `SpecOp`, `pinsert`, `Chain.submit/build/fail/finish` (`Worker`) | Pending `BTreeMap` with replace-on-insert semantics. |
| `lib.rs`: `propose`, `commit`, `prefetch`, `retarget`, `after_commit`, `finish_speculation`, `spec_ops` | `proposeOut`, `Sys.propose`, `Sys.commit`, `Sys.prefetch`, `Sys.retarget`, `specOps` (`Engine`) | The writer as a labelled transition system `Step`. |
| `root::Terms::combine`, `metadata_hash` | `rootOf`, `Hashes` (`Root`) | One formula at every height, the initial node's included (R42). |
| `proposal::Node::bare_root`, `Registry::lookup`, `RightCash::revision` | `Node.AnswersTo`, `LookupBinding` (`Engine`, `Spec`) | Which roots resolve to a node (R43); the scan order is abstracted. |
| `proposal::Node`, registry head | `Node`, `Sys.nodes`, `Sys.head` | Nodes addressed by id; the parent check of `commit` is by id. |

The transition system `Step` has two kinds of labels:

* **consensus actions**, which every validator performs identically:
  `propose p b md` (propose batch `b` with metadata `md` on node `p`) and
  `commit n`;
* **internal actions**, which are local and may differ arbitrarily between
  validators: `prefetch` hints (any node, any keys, any margin), the worker
  building a step, a worker step failing, and the speculation target being
  dropped.

The model over-approximates the Rust engine wherever timing or local
configuration is involved. The worker may build or fail a step at any moment.
The final speculative proposal may fail. Hints may arrive on any node with any
margin. Speculation may be on or off. Because every Rust behaviour is a model
behaviour, the theorems, which quantify over all model behaviours, cover the
Rust engine.

### 1.2 Trusted assumptions (not proved here)

* **A1. Correct storage engine** (as the task allows). A storage view is
  identified with its key/value state. `propose(view, batch)` applies the batch
  in order (`applyBatch`); `get` reads the state; committing a view does not
  change its contents. Metadata does not affect the stored state; the built-in
  adapters ignore it. The storage root is a function of the state
  (`ROOT_IS_STATE_FUNCTION`; `RightCash::new` refuses speculation otherwise), so
  it is modelled as `H.storage : Store K V → D`, each engine with its own
  convention for the empty state. The initial storage state is arbitrary:
  `RightCash::new` accepts an engine that already holds a chain's earlier
  state (R42). A storage call may fail; for
  worker steps this is modelled as nondeterministic failure. The writer's plain
  proposal on its parent's view does not fail on a correct engine (contract
  item 4 in `storage/mod.rs`).
* **A2. Hash functions** are uninterpreted. Nothing assumes they are injective;
  see §3.
* **A3. Vector-commitment correctness.** *Discharged* for all four schemes
  (§7.2): the digest a snapshot stores is the scheme's canonical function of
  the set. The schemes' hash functions stay uninterpreted. Their binding
  strength (a collision of the canonical function is a SHA-256/BLAKE3
  collision, or for `lthash` a lattice collision) is still assumed. The sparse
  Merkle tree also assumes, as its Rust documentation does, that distinct keys
  have distinct addresses (`SHA-256(key)`). For `merkle-blake3`, the levels
  above the leaves and the SIMD lane batching (`blake3_lanes`) are treated as
  a deterministic function of the leaf hashes.
* **A4. Data-structure refinement.** *Partly discharged* (§7.1, §7.3):
  `merge`, `normalise` and `compact` on sorted record arrays with arena slots
  are proved to implement the abstract update. Still abstracted:
  * the policies' `index` array is derived from `order`, so `merge_index` and
    the sync between the two are not modelled;
  * `split_order` is modelled as a filter;
  * `u32` offsets are `Nat`s (the Rust code panics past 4 GiB rather than wrap);
  * `Value::from_bytes` is assumed to round-trip.
* **A5. Channel semantics.** Requests reach the worker in FIFO order and are
  handled one at a time (`std::sync::mpsc`, single worker thread).
* **A6. Fixed-width encodings are injective.** The root preimage (capacity,
  height, four 32-byte digests, fixed static terms) and the policy-order
  encoding are injective, so a collision of the abstract `H.root`/`H.policy` is
  a SHA-256/BLAKE3 collision. This is argued in `Root.lean`, not proved at the
  byte level.
* **A7. Every block writes, and eviction never empties the set.** Used only
  by `LookupUnique` (§5). The consensus layer proposes no empty batch: each
  batch has at least one put or delete (`Label.Writes`; the engine does not
  check this). The policy keeps at least one key after such a batch
  (`Policy.KeepsKey`), which FIFO and LRU-write do exactly when the low
  watermark is at least 1 (`Fifo.keepsKey`, `Lru.keepsKey`).
  `validate_watermarks` accepts 0. With a low watermark of 0, an evicting
  block empties the set even though every batch writes, and the problem
  A7 exists to rule out comes back (§9).

Not modelled, because they have no effect on consensus state: handles and
reference counting, the registry ring and live index (lookup by root is
covered by a property over *every* node that answers to a root, §5),
statistics and timings,
`close`, `prune`, and checkpoint writing. Commit failures are omitted too.
They leave the head unchanged or poison the writer, which only removes
behaviours.

---

## 2. Consensus state versus local state

A node's **consensus state** (`EState`, obtained with `Node.state`) is

```
height        : Nat                      -- block height
ws            : K → Option (Entry V)     -- the buffered write set, tombstones included
policy        : P.Cons                   -- the eviction policy's consensus state
store         : K → Option V             -- the state of the node's pinned storage view
```

For FIFO and LRU-write, `P.Cons` is the eviction order: the list of
`(height, key)` pairs that `state_digest` hashes.

**Local state** consists of the prediction marks and hint bookkeeping inside
the policy (`marked`, `hinted_*`, `prediction_*`, `next_candidate`, `trigger`),
the speculation target, and the worker's chain. Local state is deliberately
outside the root (design §6.1, §9.3), so two validators with the same root can
hold different local state. This is why property 1 binds the policy's
consensus state and not its marks. Property 3 shows that the marks never
matter.

---

## 3. "With overwhelming probability"

Probabilistic statements are formalised in the standard reduction style.
`H.Broken` is the disjunction of:

* a collision of the root hash (`Collision H.root`),
* a collision of the set commitment (`Collision H.vc`),
* a collision of the policy-state digest (`Collision H.policy`),
* a collision of the storage root (`Collision H.storage`), or
* a *claw*: a combined root equal to a storage root
  (`H.root x = H.storage st`). `Revision(root)` compares one lookup key with
  both kinds of root (R43), and the `Hash` type does not separate them.

Every binding theorem has the shape *equal roots ⇒ equal states* **∨**
`H.Broken`. The proofs only take apart the preimages they are given, so
anyone holding two states that falsify the left-hand side already holds a
collision or a claw. With collision-resistant hashes, and a combined-root
hash (domain-separated SHA-256) independent of the engine's root hash, this
event has negligible probability. A claw with Firewood's MerkleDB empty-trie
root, the zero hash, is a SHA-256 preimage of zero.

Since R42 there is no height-0 case, so no event involving a constant root is
needed.

---

## 4. Reference semantics

`specPropose cap st b` (`Spec.lean`) is the consensus meaning of one `Propose`
of batch `b` on a node in state `st`. It is the *plain path* of design §9.1:

1. `(V, c') := P.specWrites st.policy (keys of b) (st.height + 1) cap`, the
   policy's eviction rule on its consensus state;
2. each key's final entry is the batch's last op on it, else the parent's entry;
3. the new write set is the final entries minus the victims `V`;
4. the new storage state is the parent's, with each victim's final entry
   written (a tombstone becomes a delete);
5. the height is `st.height + 1`.

`CSys` lifts this to a whole engine (nodes, parent links, head). `CSys.step`
gives the reference meaning of each label (internal labels are no-ops), and
`CSys.run` runs a trace. `Sys.proj` projects an engine state onto `CSys` by
forgetting all local state.

---

## 5. The properties

Throughout, `P` is the eviction policy with its consensus parameters, `H` the
hash functions, and `cap` the capacity; together they make up "the same
engine". `Reachable P H cap sys` means that `sys` arises from a valid initial
node, with speculation on or off, by any finite execution. A valid initial
node (`InitOK`) has a policy that tracks exactly its set's keys. `new` and
`recover` check this with `validate_policy_keys`
(`fifo_initOK_of_tracksExactly`, `lru_initOK_of_tracksExactly`). Its height
and storage state are arbitrary (R42: an empty or used engine under `new`, any
checkpoint under `recover`). `initNode` with `fifo_initOK_optIn` and
`lru_initOK_optIn` shows this for an empty set over any storage state.

### Property 1: root binding (`RootBinding`)

> For any two reachable engines `sys₁`, `sys₂` and node ids `i`, `j`: if
> `(sys₁.nodes i).root = (sys₂.nodes j).root`, then
> `(sys₁.nodes i).state = (sys₂.nodes j).state` (same height, same buffered
> write set, same eviction-policy state, same storage state) or `H.Broken`.

Proved: `rootBinding`, instantiated as `fifo_rootBinding` and
`lru_rootBinding`. The state-level core is `rootOf_binding`. The two engines
may have entirely different histories, hints and local settings. Since R42
the proof needs neither reachability nor the policy laws: every root,
the initial node's included, hashes the node's whole consensus state.

### Lookup by root (`LookupBinding`, R43)

`Revision(root)` resolves a node that *answers to* `root` (`Node.AnswersTo`):
its combined root, or, while its write set is empty, its storage view's root.

> For any two nodes `n₁`, `n₂` (of any engines) that answer to the same root:
> every key reads the same through both (`kvOf`), and if the root is the
> combined root of either node, `n₁.state = n₂.state`; or `H.Broken`.

Proved: `lookupBinding`, `fifo_lookupBinding`, `lru_lookupBinding`. The
statement covers every answering node, so it holds whichever one the
registry's scan order picks. A handle found by a combined root is therefore
interchangeable with any other; one found by a storage root is only
read-equivalent. `emptyBlock_bareRoot` shows that this gap is real: an empty
block on an empty-set node answers to the same storage root but has a
different consensus state and (unless `H.Broken`) a different combined root,
so blocks built on the two differ (§9).

Under A7 the gap closes within an engine (`LookupUnique`):

> In any engine reached from a valid initial node by a trace whose batches
> all write, two nodes that answer to the same root have the same consensus
> state, or `H.Broken`.

Proved: `lookupUnique`; `fifo_lookupUnique` and `lru_lookupUnique` for a low
watermark of at least 1; `async_lookupUnique` (with `fifo_`/`lru_`
instances) for the concurrent system. The key fact is
`nonempty_of_writes`: under A7 only the initial node can have an empty write
set, so it is the only node that answers by its storage root. It is proved
as an invariant of the reference semantics (`CInv`), which carries over to
both models through `refines` and `async_refines`. `Revision(r)` therefore
gives the same parent for later blocks whenever it is called.

### Property 2: deterministic transitions (`DeterministicPropose`)

> If `sys₁.nodes p₁` and `sys₂.nodes p₂` have the same root, and each engine
> takes a `propose` step with the same batch and metadata on that node, the two
> new nodes have the same consensus state and the same root, or `H.Broken`.

Proved: `deterministicPropose`, `fifo_deterministicPropose`,
`lru_deterministicPropose`. The root-only corollary is
`deterministicPropose_root`.

### Property 3: independence from prefetch (`PrefetchIndependent`, `PrefetchIndependentTraces`)

Functional form:

> In any reachable engine, a `propose p b md` step creates a node whose state
> is exactly `specPropose cap (state of p) b`, and whose metadata hash is
> `H.metadata md`.

This holds whatever hints were received, whatever the worker built or failed
to build, and whichever path (plain, chain kept, speculative finish, failed
finish) the code took.

Two-instance form:

> Two engines that start from the same consensus state and perform the same
> sequence of consensus actions (`propose`s and `commit`s), interleaved with
> *arbitrary and different* internal actions, end in the same consensus
> projection.

This covers different prefetch hints, worker timing, worker failures,
speculation on versus off, and different margins and triggers.

Proved: `prefetchIndependent` and `prefetchIndependentTraces`, with `fifo_*`
and `lru_*` instances.

### Refinement (`Refines`)

> For every execution from a valid initial node,
> `CSys.run (proj init) τ = some (proj final)`.

The engine's consensus behaviour *is* the reference semantics. Properties 2
and 3 are corollaries of this together with property 1. Proved: `refines`,
`fifo_refines`, `lru_refines`.

---

## 6. Proof architecture

1. **Policy laws** (`Policy.Lawful`). These are sixteen facts about a policy,
   proved for FIFO (`Fifo.lawful`) and LRU-write (`Lru.lawful`) from their
   code. The central ones:
   * actual victims and the next consensus state depend only on the consensus
     state (`writes_victims`, `writes_cons`), and hints never change it
     (`hint_cons`);
   * `hint_delta` and `kept_delta`: the storage ops a hint or a non-evicting
     block returns describe its mark change exactly (`MarkDelta`). Evicts are
     queued before retracts and the pending map keeps the last op per key, so
     a retracted key must end unmarked, an evicted one marked, and any other
     key unchanged;
   * `final`: an evicting block's refinement (`FinalOK`) only evicts actual
     victims, omits only victims that were predicted and not rewritten,
     retracts every retained prediction, and never retracts a victim.
2. **Prediction invariant** (`ChainOK`). Unless the chain has failed, the
   storage state the worker's chain stands for (`Chain.eff`: the latest view
   plus pending ops) equals the base view with every marked key holding the
   target's entry. `retarget` establishes it. Hints, kept blocks and worker
   steps preserve it.
3. **Finalisation lemma** (`finish_store`). Under `ChainOK` and `FinalOK`, the
   view `finish` returns has exactly the reference storage state. This is the
   heart of property 3.
4. **Global invariant** (`Inv`). Every node satisfies `NodeOK`: the policy
   tracks exactly the write set's keys, without duplicates, and the marks are
   tracked keys. The target, if any,
   satisfies `ChainOK`. `inv_step` shows that every transition preserves `Inv`.
5. **Simulation** (`proj_step`). Each engine step maps to one reference step
   on the projection. Induction gives `refines`, and the properties follow.

---

## 7. Implementation layer: snapshot, arena, commitment schemes

The engine model of §1–§6 treats a node's write set as a map and its
commitment as `H.vc` of that map. This section proves that the Rust data
structures implement exactly that.

### 7.1 `Snapshot::apply` (`Impl/Merge.lean`, `Impl/Snapshot.lean`)

* `merge_spec` covers `set::merge`, transcribed as recursion over the
  parent's sorted records, the normalised batch and the sorted victims. On
  sorted inputs whose victims are present:
  * the output is sorted;
  * it stands for `childWS`, the engine model's child map;
  * it evicts exactly the victims with their final entries, in victim order
    (the plain path's storage batch);
  * it reports every changed key exactly once, in ascending order, with its
    true old and new entries. This is `CallsOK`, the contract of
    `VectorCommitment::apply`.

  `merge_map` shows the loop is independent of the payload, so the same
  theorem covers entries and arena slots.
* `Snap.snap_apply` covers the whole `Snapshot::apply`: pack the batch into a
  chunk, sort and deduplicate the ops (last op wins), merge, optionally
  compact, then commit. If the parent is well formed (sorted records, every
  slot in bounds, the scheme instance representing the set, digest = `F` of
  the set), then:
  * the child is well formed;
  * its entries are `childWS` of the parent's;
  * its evicted entries are the engine model's;
  * its stored digest is `F` of its sorted entries.

  `Snap.genesis_ok` covers the initial snapshot. By induction, every snapshot
  of every chain of proposals satisfies the engine model's abstraction.
  `Snapshot::restore` performs the same steps from an empty parent.

  `snap_apply` takes the victims as strictly sorted by the key order and
  present in the parent or the batch. The second condition is the policy law
  `victims_sub`. The first holds because the v0 policies sort victims with
  `le`, which is assumed to be the non-strict form of that same order (the
  `Ord` on key bytes).

### 7.2 Commitment schemes (`Impl/VC.lean`, `Impl/SparseMerkle.lean`, `Impl/MerkleBlake3.lean`)

`VCImpl.Correct X F Rep` means: the instance `Rep`resents the set it was
built for, and after any calls satisfying `CallsOK`, `commitment` returns
`F L'` of the child's sorted entries and represents the child.
`VCImpl.digest_of_set` (via `sorted_ext`) makes `F` a function of the set.

| Scheme | Theorem | What the proof establishes |
|---|---|---|
| `rehash` | `rehash_correct` | stateless; the digest is the hash of the sorted entries |
| `lthash` | `lthash_correct` | the incrementally maintained lane sum equals the sum of the items of the current set (abelian-group laws of wrapping `u16` lanes, `lanes`) |
| `merkle` (sparse) | `SMT.smt_correct` (via `SMT.up_spec`) | after each path update, every stored node equals the recursive subtree hash; addresses assumed collision-free |
| `merkle-blake3` | `MB3.mb3_correct` (via `MB3.fill_spec`) | when `fill_leaves` succeeds, every reused leaf (indexed `parent[untouched + replaced]`) is the correct leaf hash; otherwise the full rebuild is used. The tree is always the full build's |

### 7.3 The value arena (`Impl/Arena.lean`)

* `pack_read` shows that each slot `normalise` creates reads back its op's
  value. `read_append` shows that the parent's slots read the same bytes in
  the child's arena.
* `compact_decode` and `compact_wf` show that compaction preserves every
  record's entry and keeps every slot in bounds of the new chunk.
* **No use after free** (`referenced_not_freed`). Chunks are `Arc<[u8]>`, so a
  chunk is freed only once no live arena holds it (`Freed`). In a
  well-formed snapshot, every value slot points into one of the snapshot's
  own chunks, within bounds. Hence a chunk referenced by a live revision is
  never freed. `snap_apply` and `genesis_ok` establish well-formedness for
  every snapshot.

---

## 8. Concurrency (`Concurrent/Model.lean`, `Concurrent/Proofs.lean`)

### 8.1 The concurrent model

The synchronous model applies a worker request when it is sent. The
concurrent model `ASys`/`AStep` makes the worker a thread:

* **Writer.** It sends `Submit`/`Reset`/`Finish` into a FIFO channel without
  waiting. A speculative `Propose` is split into `proposeBegin` (send
  `Finish`, block) and `proposeEnd` (receive the reply, install the child,
  retarget). No other writer step can run while the writer is blocked.
* **Worker thread.** At any moment it may dequeue the oldest request, or build
  a step from its pending ops, or fail to build it.
* **Hint sources** (any number of threads, each holding handles to any nodes).
  `prefetch` takes `&mut self`, so the hints are serialised with every other
  writer operation, in any order. The model allows any interleaving.
* **Handle drops** may kill the target at any time.
* **Readers** (`Reader`, `Handle`) change nothing (§8.3).

### 8.2 Results

* `ainv_step`: every interleaving preserves `AInv`. The writer reasons about
  the *logical* chain, which is the worker's chain after it drains the
  channel (`logical`). The worker's own actions change that chain only up to
  `ChainSub` (same effective state, or failed), which preserves `ChainOK`.
  While the writer is blocked, the queued `Finish` sits behind a chain that
  satisfies `ChainOK` for the parent, so the reply is the reference store.
* `async_refines`: every concurrent execution's consensus projection is the
  reference run of its consensus actions.
* **Properties 1–3, concurrently:**
  * `async_rootBinding` (and `lookupBinding`, which is about nodes and so
    applies to both models);
  * `async_deterministicPropose`;
  * `async_prefetchIndependent`;
  * `async_prefetchIndependentTraces`: two instances that perform the same
    proposes and commits under *any two schedules* of worker threads, hints
    and handle drops end in the same consensus state.

  Each has FIFO and LRU instances in `Main.lean`.

### 8.3 Readers

* `read_stable`: once a node exists, nothing that runs concurrently changes
  its consensus state or any read through it (`kvOf`, which is `Node::get`).
  This covers writer operations, hints, the worker thread and handle drops. A
  `Reader::get` therefore returns the value of the node it resolved under the
  registry lock: reads are linearisable at that point.
* `read_specPropose`: after `Propose(b)` a key reads as `b`'s last write to
  it, or else exactly as before. Eviction to storage is invisible to readers.

### 8.4 Trust boundary for thread safety

The Lean model fixes the atomicity of actions. The following are what make
that atomicity sound in the Rust code, and they are not proved in Lean:

* **Exclusive writer operations** come from the borrow checker: every writer
  operation takes `&mut self`.
* **Freedom from data races on non-atomic memory** comes from `Send`/`Sync`.
  All shared mutable state sits behind `Mutex`, atomics or the channel, and
  the compile-time test `send_sync` in `lib.rs` asserts this.
* **Locks and channels are linearisable**: `parking_lot::Mutex` and
  `std::sync::mpsc` have the standard semantics.
* **The storage adapter is thread-safe** under concurrent reads and proposals
  from the writer and the worker. This is part of A1, including
  `RevisionStale`/`ProposalOrphaned` as errors (modelled as step failures),
  never wrong data.
* **Relaxed atomic counters** (`Stats`, timings) are non-consensus and not
  modelled.

---

## 9. Findings

* **Resolved in `d34dd27`: the initial root binds the policy state.** At
  `1f5e080`, `Terms::combine` returned the constant `EMPTY_ROOT` at height 0
  without reading its inputs, and `RightCash::new` did not check the policy.
  Two engines could share the initial root with different eviction orders,
  and then diverge on the same batch. R42 removed the height-0 case. The
  model no longer has a genesis precondition (`GenesisOK` is gone), and
  `rootBinding` holds for any two nodes. Rerunning the reproduction at
  `d34dd27`, the two engines now have different initial roots.
* **Resolved in `ce7dba2`: `new` checks that the policy tracks exactly the
  set's keys.** At `d34dd27` only `recover` checked it, and a policy that
  already tracked a key passed `new` and later crashed a block in `merge`
  (`set.rs:716`). `from_snapshot`, which both `new` and `recover` run, now
  calls `validate_policy_keys` (`tracks_exactly`: the policy's `index`
  equals the set's keys). Given A4 (`index` is the order's keys in key
  order), this is exactly `InitOK` (`fifo_initOK_of_tracksExactly`), so the
  model's one precondition on the initial node is now checked at runtime.
  The reproduction is refused at `ce7dba2` with `InvalidConfig`.
* **R43: a storage root does not name a unique node unless A7 holds.** Every
  node with an empty write set answers to its storage view's root. At
  `d34dd27`, with a `MemoryStorage` that already held a key:

  1. before the first block, `revision(engine_root)` was the initial node;
  2. an empty first block was proposed on it and committed;
  3. `revision(engine_root)` then returned that block, not the initial node;
  4. the same batch proposed on the two handles gave different roots.

  Under A7 this cannot happen (`lookupUnique`): only the initial node ever
  has an empty write set. Both halves of A7 are needed. With a low
  watermark of 0, nonempty batches reproduce it at `ce7dba2`: over an engine
  holding `a = v`, with capacity 1, block 1 rewrites `a = v` and block 2
  deletes the absent key `b`. Block 2 evicts both keys, which writes `a = v`
  and deletes `b`, so the set is empty and the storage state is the
  original one. `revision(engine_root)` then returns block 2. Neither half is
  checked by the engine. To check them instead of assuming them, `propose`
  could reject an empty batch and `validate_watermarks` a low watermark of 0.
* No counterexample to properties 1–3 exists in the model. In particular, the
  speculative path (prediction marks, kept chains spanning several blocks,
  margin-induced retractions, LRU withdrawals and cursor refills, worker
  failures at any point, retargeting on commit and prefetch) always produces
  the plain path's storage state.

---

## 10. Pinning and traceability

### 10.1 Which commit is proved

The RightCash repository is the submodule `rust/`, pinned at the commit the
model is about (`ce7dba2`). `git submodule status` shows the pin.
Moving to a new Rust commit is a reviewable change:

```sh
git -C rust fetch && scripts/check_trace.sh   # which mapped files changed?
git -C rust checkout <new-commit>             # after re-checking those proofs
scripts/check_trace.sh && git add rust TRACEABILITY.md
```

This is the layout AWS uses for Cedar: the Lean models live in `cedar-spec`,
which pins `cedar` as a submodule. The alternative, if code and proofs will
evolve together, is to keep the Lean project in the Rust repository (for
example under `verification/`). A proof is then checked against exactly the
code in the same commit, and CI can reject a pull request that breaks either
side.

### 10.2 Rust ↔ Lean correspondence

* Every Lean definition's docstring names the Rust item it models.
* `scripts/trace.tsv` is the machine-readable map: Rust file, a literal
  symbol, the Lean name, and how they relate (transcribed, equivalent,
  abstracted, assumed, over-approximated). `scripts/check_trace.sh` checks
  that every symbol still occurs at the pinned commit and every Lean name
  still exists. It regenerates `TRACEABILITY.md`, whose rows link to the Rust
  line in `rust/` and to the Lean declaration. It also lists the mapped Rust
  files that differ between the pin and `origin/main` (or a given ref), i.e.
  the proofs to re-review before a bump.

### 10.3 Checking the model against the code

The traceability check is syntactic. To test semantically that the model
matches the code, compare executions. The Lean definitions are computable,
so `lake` can build an executable that runs random batch and hint traces
through the model and prints the roots, while the Rust test suite runs the
same traces. Cedar uses this kind of differential testing alongside its
proofs.

---

## 11. Not yet covered: suggested next steps

1. **No-panic theorem.** Show that reachable states never reach the Rust
   `unreachable!`/`expect`/capacity `assert!` sites. Most of the ingredients
   are already invariants: victims are present, final evicts are victims,
   marks are tracked keys, and slots are in bounds. The capacity bound needs a
   length invariant on the order.
2. **Byte-level encodings and scheme binding** (A3, A6). Prove injectivity of
   the root preimage, the `order_digest` encoding and the entry-item encoding
   over `List UInt8`. Then reduce collisions of each scheme's `F` to
   SHA-256/BLAKE3 collisions (Merkle binding for both trees).
3. **Policy index structures** (A4): `merge_index` and the `index`/`order`
   synchronisation.
4. **Checkpoint recovery**: `persist::encode` followed by `Snapshot::restore`
   round-trips the consensus state.
5. **Differential testing** of model against code (§10.3).

---

## 12. Layout and build

```
RightCash/Basic.lean              entries, batches, stores; last-writer-wins lemmas
RightCash/Root.lean               hashes, root composition, rootOf_binding
RightCash/Policy.lean             eviction-policy interface and laws
RightCash/Worker.lean             speculation worker: chains, finish, eff lemmas
RightCash/Engine.lean             the writer as a labelled transition system
RightCash/Spec.lean               reference semantics and the property statements
RightCash/Proofs/*.lean           invariants, finish_store, properties 1–3
RightCash/Proofs/Lookup.lean      lookup by root under A7 (lookupUnique)
RightCash/Policies/*.lean         FIFO and LRU-write, and their laws
RightCash/Impl/Sorted.lean        key order, sorted record lists, sorted_ext
RightCash/Impl/Merge.lean         set::merge and merge_spec
RightCash/Impl/Arena.lean         value arena, normalise, compact, referenced_not_freed
RightCash/Impl/VC.lean            VectorCommitment framework, rehash, lthash
RightCash/Impl/SparseMerkle.lean  vc::merkle
RightCash/Impl/MerkleBlake3.lean  vc::merkle_blake3
RightCash/Impl/Snapshot.lean      Snapshot::apply end to end (snap_apply)
RightCash/Concurrent/*.lean       worker thread, channel, readers
RightCash/Main.lean               results instantiated for FIFO and LRU-write
scripts/Audit.lean                prints the axioms of the main theorems
scripts/trace.tsv, check_trace.sh Rust ↔ Lean map and its checker (§10)
rust/                             the RightCash repository (submodule, §10.1)
```

```sh
source ./env.sh        # project-local Lean 4.35.0 in ./.toolchain
lake build
lake env lean scripts/Audit.lean
scripts/check_trace.sh   # regenerates TRACEABILITY.md (needs rust/)
```
