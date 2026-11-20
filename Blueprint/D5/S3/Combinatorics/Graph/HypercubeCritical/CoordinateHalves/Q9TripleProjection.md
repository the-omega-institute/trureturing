# Missing patterns at distance two force a smaller half

## Abstract

A coordinate half bound from two missing patterns

**Theorem 1.1 (The half containing both missing patterns has at most 24 vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TripleProjection.half_card_le_of_missing_triple_patterns`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TripleProjection.half_card_le_of_missing_triple_patterns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a Huang-balanced induced cubic support of order 72, consider two missing patterns of a three-coordinate projection. If they differ at two coordinates, the coordinate where they agree selects a half of size at most 24.

Coordinate permutations and bit flips preserve the hypotheses through signed Huang covariance. Normalize the missing patterns to 001 and 111. At every selected vertex on the common side, the two exterior signed rows force two translations into the other half. The same rows show that the two images are disjoint. Counting the original half and both images gives the bound.

For the order-72 branch of Hong, Wu and Xia, arXiv:2610.09483v1, Section 7, Problem 2, this restricts which patterns can be missing when the coordinate halves are large.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TripleProjection.half_card_le_of_missing_triple_patterns`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance](../HuangCubeCovariance.md)
