# When a rooted exploration first observes a cycle

## Abstract

The edge that closes the first cycle in an exploration with complete neighborhoods.

**Theorem 1.1 (Criterion for a first observed cycle).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/FirstObservedCycle.first_observed_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/FirstObservedCycle.first_observed_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start from a root in a finite simple graph. At every step query the complete neighborhood of a vertex reachable from the root through exposed edges. The exposed graph contains exactly the original edges incident to vertices already queried. Assume this graph is acyclic before the next query. The reply creates a cycle exactly when the next vertex has never been queried and it has a neighbor that is also unqueried and reachable from the root before the query. Adding that edge joins two vertices already connected by exposed edges. When every new edge reaches an isolated vertex, these edges add only leaves.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/FirstObservedCycle.first_observed_cycle`
