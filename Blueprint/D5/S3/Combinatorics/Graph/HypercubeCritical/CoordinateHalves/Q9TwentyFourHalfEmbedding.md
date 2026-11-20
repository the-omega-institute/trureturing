# Exclusion of a 24-vertex half in the nine-cube

## Abstract

Q9TwentyFourHalfEmbedding

**Theorem 1.1 (An order-72 Huang-balanced induced cubic support has no 24-vertex half).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyFourHalfEmbedding.no_twenty_four_half`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyFourHalfEmbedding.no_twenty_four_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a putative 24-vertex half, suppress the twelve independent degree-two vertices. The result is a connected triangle-free cubic graph on twelve vertices. The parity of the remaining vertices identifies the six edges already present in the half and the twelve edges created by suppression. The graph and parity certificates cover every realized half by 53 expanded models.

Translate the first vertex to the origin and number each in-plane axis when it first appears. The parent edges and Hamming distance tests cover every induced cube embedding of a listed model in this normalization.

For every enumerated placement the parity reconstruction counts at least 52 occupied positions in the opposite half. The reconstruction theorem from the 22-vertex branch identifies this count with the actual opposite cardinality, which would have to equal 48. The exclusion applies to either side of the coordinate-zero cut.

This is an order-72 component obstruction for Problem 2 of Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, Section 7 (https://arxiv.org/html/2610.09483v1#Thmproblem2).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyFourHalfEmbedding.no_twenty_four_half`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance](../HuangCubeCovariance.md)
