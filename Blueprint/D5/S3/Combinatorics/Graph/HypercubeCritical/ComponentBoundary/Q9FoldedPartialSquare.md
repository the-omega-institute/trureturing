# An obstruction from three negative squares

## Abstract

Three negative squares can rule out a folded signed row before its fifth edge is determined.

**Theorem 1.1 (Four forced signs exceed the centre target).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedPartialSquare.three_negative_squares_obstruct_row`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedPartialSquare.three_negative_squares_obstruct_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let u be a centre with finite neighbour row N(u) and four distinct neighbours b, c₁, c₂ and c₃. Take the four incidences around each square u, b, dᵢ, cᵢ, u. Assume each square has negative sign product and each opposite corner dᵢ has exactly the neighbours b and cᵢ. The signs of b–dᵢ and cᵢ–u agree with their reversals, so the square product uses the same signs as the rows at u and dᵢ. For any vertex switch under which the three exact corner rows sum to zero, if N(u) has size at most five then its signed sum differs from every integer target of absolute value at most two.

Vertex switching adds the two endpoint bits to each edge bit over the field of two elements. On a square each switch bit occurs twice, so its sign product is preserved. The two corner terms sum to zero and thus have opposite signs. Since the square is negative, the two edges at u have equal signs. Applying this to all three corners fixes the relative signs of the four centre terms. Their sum is +4 or −4. The remaining terms number at most one and have total magnitude at most one, so the centre row has magnitude at least three. For switching in signed graphs, see https://arxiv.org/html/1303.3083#S1.SS7

Fold Q₉ along its last coordinate and use the Huang signs, where an edge sign is the parity of the coordinates preceding its direction. In each transverse coordinate square, changing the earlier coordinate reverses the sign on precisely one pair of parallel edges, giving a negative product. At a folded singleton u, let N(u) consist of the opposite-layer singleton neighbours. The selected endpoint of u has three occupied neighbours on transverse slots, so at most five of the eight slots can contribute to N(u). If k(u) is the number of neighbouring dimers, each uses one of those three occupied slots, so 0 ≤ k(u) ≤ 3.

With selected labels satisfying the occupied signed edges and the missing-endpoint Huang row equal to zero, the folded row calculation in Q9FoldedSignedRows gives the target p(u)(k(u) − 1), where p(u) is the axial sign. Its absolute value is at most two. Thus three opposite corners whose opposite-layer rows each have degree two and k = 1 provide the exact zero rows in the theorem. The centre obstruction applies to every completion that preserves these three corner rows and the four specified centre incidences, regardless of the status of the other centre slots.

A finite unsigned example uses bit coordinates (x₁, x₂, x₃, x₄, r, s, t, h, ℓ). Select sites with x₂ + x₃ + x₄ ≤ 1 and with the parity of the first four bits equal to r XOR ℓ when r = s and to r XOR t otherwise. The 128 selected sites induce an unsigned cubic graph, and every unselected site has even occupied degree. Folding along ℓ gives eight copies of three squares sharing an edge. Each singleton has k = 1. For each copy, exact enumeration gives feasibility for all 28 separate row pairs and four vertex switches satisfying the modulo-four equations and all six degree-two exact rows. It also gives six unsigned negative-degree assignments and zero switches satisfying the full exact integer system. The support contains occupied coordinate squares. This example concerns unsigned occupancy and feasibility of the folded row tests. The value of f₂(Q₉) in Hong, Wu and Xia's Problem 2 remains open. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedPartialSquare.three_negative_squares_obstruct_row`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSignedRows](Q9FoldedSignedRows.md)
