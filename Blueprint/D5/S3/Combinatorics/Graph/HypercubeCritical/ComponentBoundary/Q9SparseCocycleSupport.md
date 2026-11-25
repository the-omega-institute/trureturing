# The possible sparse pivot graphs

## Abstract

The possible sparse pivot graphs

**Theorem 1.1 (The possible sparse pivot graphs).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseCocycleSupport.sparse_cocycle_support`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseCocycleSupport.sparse_cocycle_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The degree cap and the forced triples leave a three-spoke star or a four-cycle. Each edge has two forced triples containing it, exhausting its pair cap. This gives counts of six or eight triples outside the pivot.

**Theorem 1.2 (Triples through the isolated vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseCocycleSupport.sparse_pivot_graph_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseCocycleSupport.sparse_pivot_graph_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the four-edge case, the graph is a cycle on four vertices. Adjoining either isolated vertex to a cycle edge gives a triple with exactly one edge. These two triples exhaust the capacity of that edge, determining the entire family outside the pivot.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseCocycleSupport.sparse_cocycle_support`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseCocycleSupport.sparse_pivot_graph_classification`
