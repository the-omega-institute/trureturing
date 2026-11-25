# Eight-column rigidity of the occupied graph

## Abstract

Eight-column rigidity of the occupied graph

**Theorem 1.1 (Occupied triangles share a single occupied row).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarRigidity.occupied_edge_triangle_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarRigidity.occupied_edge_triangle_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Huang curvature forbids three pairwise opposite signed contributions at a common empty row. Therefore every occupied graph triangle has a common occupied row, and the three-contact cap prevents one edge from lying in two triangles.

**Theorem 1.2 (Complete bipartite equality forces a full empty-row neighborhood).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarRigidity.occupiedK44_star`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarRigidity.occupiedK44_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a four-by-four occupied graph, root-neighbor double flips use the four occupied axes and empty partner axes. The other three vertices on the root side force all empty partners to agree. The eight columns are precisely the neighbors of the resulting empty row.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarRigidity.occupiedK44_star`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarRigidity.occupied_edge_triangle_unique`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCardinalityGap](PrimeContactCardinalityGap.md)
