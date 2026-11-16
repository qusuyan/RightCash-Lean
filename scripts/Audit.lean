import RightCash
-- Lists the axioms each main theorem depends on. Expected: only Lean's
-- standard `propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`.
#print axioms RightCash.fifo_rootBinding
#print axioms RightCash.fifo_deterministicPropose
#print axioms RightCash.fifo_prefetchIndependent
#print axioms RightCash.fifo_prefetchIndependentTraces
#print axioms RightCash.fifo_refines
#print axioms RightCash.lru_rootBinding
#print axioms RightCash.lru_deterministicPropose
#print axioms RightCash.lru_prefetchIndependent
#print axioms RightCash.lru_prefetchIndependentTraces
#print axioms RightCash.lru_refines
#print axioms RightCash.fifo_async_refines
#print axioms RightCash.lru_async_refines
#print axioms RightCash.fifo_async_prefetchIndependentTraces
#print axioms RightCash.lru_async_rootBinding
#print axioms RightCash.async_deterministicPropose
#print axioms RightCash.read_stable
#print axioms RightCash.read_specPropose
#print axioms RightCash.rehash_ok
#print axioms RightCash.lthash_ok
#print axioms RightCash.merkle_ok
#print axioms RightCash.merkleBlake3_ok
#print axioms RightCash.Snap.snap_apply
#print axioms RightCash.Snap.genesis_ok
#print axioms RightCash.Arena.referenced_not_freed
#print axioms RightCash.Arena.compact_decode
#print axioms RightCash.merge_spec
