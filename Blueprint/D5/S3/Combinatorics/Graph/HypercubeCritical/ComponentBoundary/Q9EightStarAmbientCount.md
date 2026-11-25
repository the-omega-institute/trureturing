# Ambient size constraint of the eight-star

## Abstract

Ambient size constraint of the eight-star

**Theorem 1.1 (Two disjoint sixteen-vertex families).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarAmbientCount.eight_star_ambient_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarAmbientCount.eight_star_ambient_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sixteen lifted spokes and the third neighbors of the sixteen selected mixed corners lie in one projected parity. A repeated third neighbor would form a selected square, violating balance.

**Theorem 1.2 (Eight-star completion requires at least ten paired fibres).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarAmbientCount.directionEdges_ge_ten_of_eight_star`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarAmbientCount.directionEdges_ge_ten_of_eight_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occupied-fibre identity gives three times the projected-parity vertex count as eight times the paired count plus twice its parity part. The thirty-two vertices force a paired count of at least ten.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarAmbientCount.directionEdges_ge_ten_of_eight_star`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarAmbientCount.eight_star_ambient_count`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCardinalityGap](PrimeContactCardinalityGap.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OccupiedFibreParity](Q9OccupiedFibreParity.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CubeSmallSupport](../CubeSmallSupport.md)
