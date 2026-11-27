# Common neighbors at a cubic contact edge

## Abstract

Adjacent cubic vertices in the distance-two contact graph have either zero or two common neighbors.

**Theorem 1.1 (A common neighbor of a cubic contact edge has a companion).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactGraphTriangles.cubic_edge_common_neighbor_has_companion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactGraphTriangles.cubic_edge_common_neighbor_has_companion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An edge whose endpoints both have degree three has two remaining neighbors at each endpoint. If the endpoints share one of these neighbors, the two remaining neighbor sets must coincide. This constraint applies regardless of the shared neighbor's degree and is preserved by coordinate relabeling.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactGraphTriangles.cubic_edge_common_neighbor_has_companion`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9CubicContactCommonPartner](Q9CubicContactCommonPartner.md)
