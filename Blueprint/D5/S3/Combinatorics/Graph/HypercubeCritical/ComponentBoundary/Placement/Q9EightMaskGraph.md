# The structure of an eight-edge graph

## Abstract

A minimum-degree-three graph with eight edges is complete on five vertices with two disjoint edges removed.

**Theorem 1.1 (Eight edges force five vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9EightMaskGraph.eight_edge_family_eq_delete_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9EightMaskGraph.eight_edge_family_eq_delete_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The degree sum bounds the support by five vertices. Eight edges require all five. Deleting two incident edges would give their common endpoint degree two, so the deleted pair is a matching.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9EightMaskGraph.eight_edge_family_eq_delete_two`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/MinimumContactDisplacementCount](MinimumContactDisplacementCount.md)
