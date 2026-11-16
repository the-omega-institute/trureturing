# Excluding unit support thirty

## Abstract

The original Huang integer operator has no negative-three eigenvector with values zero or plus/minus one and support exactly thirty.

Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2), asks whether f₂(Q₉)=3 or 4 (the 258-vertex question). The original external problem remains unresolved here; literature novelty is unconfirmed. Throughout, intA and intCoeff retain the original FALSE-prefix signed Huang integer operator and coefficients from HuangIntegralNormGap.

**Theorem 1.1 (No unit negative-three eigenvector has support exactly thirty).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitThirtyGap.no_unit_negative_three_support_thirty`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitThirtyGap.no_unit_negative_three_support_thirty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r : Q9 → ℤ, the assumptions are exactly heig: intA r = −3r, hu: every r(x) is 0, 1, or −1, and hcard: |{x : r(x) ≠ 0}| = 30. The theorem no_unit_negative_three_support_thirty(r, heig, hu, hcard) concludes False.

Apply HuangUnitThirtyStructure to S = supp(r). It supplies actual degrees three or five and an actual opposite edge xy with intCoeff(x,y) r(x) r(y) = +1. Consequently opposite_count(x) is positive. The original identity 2 opposite_count(x) + 3 = degree_S(x) therefore forces degree_S(x) = 5.

The total squared norm is thirty. parity_norms gives squared norm fifteen for both evenPart r and oddPart r; unit values convert these to actual support cardinalities fifteen. parts_eigen gives intA(evenPart r) = −3 oddPart r and intA(oddPart r) = −3 evenPart r, so every original row of either part is divisible by three.

Choose q to be the part of parity opposite x: oddPart r when cubeParity(x) is false, and evenPart r when it is true. Every actual cube neighbor of x has that opposite parity. Hence supp(q) ∩ N(x) = supp(r) ∩ N(x), as equality of the actual support-neighbor filters, and q has exactly five support neighbors at x. Apply CubeFiveNeighborGap.sixteen_le_support_card_of_neighbor_card_eq_five to q, its unit values, its row divisibility, x, and this five-neighbor equality. It gives 16 ≤ |supp(q)| = 15, a contradiction. The sixteen-point bound is applied to this fifteen-point parity part, not to the full thirty-point support.

A consumed private helper also bounds the support of a nonzero unit positive-three eigenvector below by thirty-six. The parity sign change r = evenPart h − oddPart h gives a unit negative-three eigenvector with the same actual support, excluding support thirty. The existing thirty-point lower bound and divisibility by six of integer eigennorms then give thirty-six. This helper is consumed by the actual five-edge-cut bound; the original 258-point question remains unresolved.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitThirtyGap.no_unit_negative_three_support_thirty`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CubeFiveNeighborGap](CubeFiveNeighborGap.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitThirtyStructure](HuangUnitThirtyStructure.md)
