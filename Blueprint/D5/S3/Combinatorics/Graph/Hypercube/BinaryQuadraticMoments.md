# Quadratic moments of binary cube supports

## Abstract

Quadratic moments of binary cube supports

**Definition 1.1 (Pair moments of a cube word).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/BinaryQuadraticMoments.pairMoment`

*Formalization.* `D5/S3/Combinatorics/Graph/Hypercube/BinaryQuadraticMoments.pairMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For distinct coordinates the pair moment sums the word over the vertices where both coordinates equal one. The diagonal is set to zero.

**Theorem 1.2 (Coordinate potentials for the pair moments).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/BinaryQuadraticMoments.exists_pairMoment_eq_add`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube/BinaryQuadraticMoments.exists_pairMoment_eq_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In odd dimension the pair moments of a binary adjacency fixed word are sums of one potential per coordinate. Each coordinate flip is an involution, so cube adjacency is self-adjoint. The coordinate contraction writes any fixed word as the image of adjacency plus the identity. Pairing against another fixed word therefore gives zero. On a triangle the sum of the three pair monomials is fixed because every linear correction from the coordinate flips occurs twice. The triangle equations recover all pair moments from the moments at one base coordinate.

For a Huang-saturated cubic support, reducing the unit signed eigenrow equation modulo two gives a fixed binary indicator. In Hong, Wu and Xia's nine-cube problem, the 36 off-diagonal moments are determined by the eight moments at a chosen base coordinate. This supplies 28 linear parity equations on candidate supports. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/BinaryQuadraticMoments.exists_pairMoment_eq_add`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/BinaryQuadraticMoments.pairMoment`
- Dependency: [D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment](BinaryKernelCoordinateMoment.md)
