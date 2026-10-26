# CyclicIntervals

## Abstract

Auxiliary finite cut-counting structure for mutual-visibility reconfiguration.

**Theorem 1.1 (A component above rank two has a small-degree member).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/CyclicIntervals.high_rank_component`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/CyclicIntervals.high_rank_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Fix one surviving component after an actual configuration cut. If all its configurations have at least three labels, some configuration in it has degree at most the cut size.

Proper nonempty cyclic intervals have a unique initial vertex: it is selected and its predecessor is not. Their distinct starts supply disjoint deletion chains. The finite-index construction transports these intervals through an injective labeling of an arbitrary selected set. If a surviving component has no configuration of rank below three, choose a configuration of maximum rank m. Its m internal cyclic deletion chains end at forbidden singletons and yield m distinct cuts. For each outside label, every actual slide starts a separate chain of proper y-containing cyclic intervals ending at a forbidden pair. The proper-chain count requires only exclusion of its two-label endpoints and remains valid when larger or unrelated two-label configurations survive. The unique interval start separates these chains. Any feasible addition has rank m+1 and is itself cut, separately from those proper chains. Partitioning actual neighbors by their unique outside label and combining the disjoint cut classes gives a vertex of degree at most the cut size.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/CyclicIntervals.high_rank_component`
- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments](PairPayments.md)
