# Large balanced components have common exterior neighbors

## Abstract

Large balanced components have common exterior neighbors

**Theorem 1.1 (At least twelve pairs have Hamming distance two).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CommonBoundaryObstruction.distance_two_pairs_card_ge_12`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CommonBoundaryObstruction.distance_two_pairs_card_ge_12` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two disjoint closed Huang-balanced cubic components of order at least 72 in a 258-vertex subcubic set have at least twelve ordered cross pairs at Hamming distance two.

Deleting one coordinate gives a bijection from each parity side of the nine-cube to the eight-cube. Neighborhoods across parity become closed neighborhoods after this folding. The coordinate-slice degree constraints and the seven-cube neighborhood recurrence give at least 130 exterior neighbors for each component.

Closedness puts both exterior boundaries in the 254-point complement, so they intersect in at least six vertices. Each common neighbor contributes at least four pair incidences by the exterior parity equation. A distance-two pair has exactly two common neighbors.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CommonBoundaryObstruction.distance_two_pairs_card_ge_12`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations](Q9BoundaryEdgeTranslations.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CubeSmallSupport](../CubeSmallSupport.md)
