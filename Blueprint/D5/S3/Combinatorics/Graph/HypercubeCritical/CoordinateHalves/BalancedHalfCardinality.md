# Size and parity of balanced cubic coordinate halves

## Abstract

BalancedHalfCardinality

**Theorem 1.1 (The cut size controls the cardinality of each half).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BalancedHalfCardinality.half_cardinality`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BalancedHalfCardinality.half_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a Huang-balanced cubic support of order six times q in the nine-cube, each coordinate cut has q edges. Each half has exactly q degree-two vertices, and those vertices are independent.

The two edges at each degree-two vertex enter the cubic vertices of the half. Counting those incidences gives the lower bound of five thirds of q. The equal degree sums on the two bipartition classes give the parity of q.

For an order-72 component in a candidate for Hong–Wu–Xia's Problem 2, the half must have even cardinality and at least twenty vertices.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BalancedHalfCardinality.half_cardinality`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeLowerBound](../BalancedCubeLowerBound.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CubicFiftyFourReconstruction](../CubicFiftyFourReconstruction.md)
