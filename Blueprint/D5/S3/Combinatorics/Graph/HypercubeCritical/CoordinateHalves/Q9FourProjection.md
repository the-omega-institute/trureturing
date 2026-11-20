# Every four-coordinate projection has at least eight points

## Abstract

Four-coordinate projection sizes in the nine-cube

**Theorem 1.1 (The four-coordinate projection bound).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourProjection.four_projection_card_ge_eight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourProjection.four_projection_card_ge_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the support be Huang-balanced and induced cubic with 72 vertices. Assume that every coordinate half has at least 30 vertices. Every choice of four distinct coordinates realizes at least eight patterns.

A missing pattern on three of the four coordinates corresponds to a complement edge along the dropped axis. The constraints on pairs and triples force any two such edges to be antipodal. If the projection has at most seven points, counts in the four coordinate matchings force exactly seven and make every complement edge occur with its antipode.

The nine-point complement has an unpaired vertex. It is isolated in the complement, so its four neighbors and its antipode belong to the projection. Translating this vertex to zero gives a missing weight-three point whose three weight-two neighbors also belong to the projection. This gives the eighth point and excludes the assumed size.

The bound applies to the order-72 branch of Hong, Wu and Xia, arXiv:2610.09483v1, Section 7, Problem 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourProjection.four_projection_card_ge_eight`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjection](Q9PairProjection.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TripleProjection](Q9TripleProjection.md)
