# Every coordinate pair attains all four patterns

## Abstract

Two-coordinate projections of a balanced cubic nine-cube support

**Theorem 1.1 (Surjectivity of the two-coordinate projections).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjection.pair_projection_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjection.pair_projection_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider a 72-vertex Huang-balanced induced cubic support in the nine-cube, with at least 30 vertices on either side of each coordinate. A missing two-bit pattern makes the two specified sides disjoint. At most twelve vertices lie in the opposite two-bit fiber.

The Huang operator gives twelve edges in each direction. The endpoints opposite the missing pattern all lie in that fiber, so both sets of endpoints fill it. A third edge at any vertex stays in the fiber. Applying one projected coordinate flip at both endpoints creates a square, which Huang balance forbids.

The statement quantifies over every coordinate pair and every bit pattern. It excludes all translates and coordinate permutations of the nine-point grid projection in the order-72 case of Hong, Wu and Xia, arXiv:2610.09483v1, Section 7, Problem 2. The value of f₂(Q₉) remains open in this development.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjection.pair_projection_surjective`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum](../BalancedCriticalSpectrum.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth](../BalancedCubeGirth.md)
