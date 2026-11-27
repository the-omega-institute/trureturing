# Residual switching rank of folded signed rows

## Abstract

The binary Laplacian computes the residual switching rank for exact integer signed rows.

**Theorem 1.1 (The Laplacian computes the residual quotient dimension).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedCycleRank.residual_rank_add_twice_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedCycleRank.residual_rank_add_twice_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let B be a binary vertex-by-edge matrix and write C for the kernel of incidence multiplication. The bicycle subspace is the intersection of C with the range of transpose multiplication. The residual quotient consists of cycles modulo these bicycles.

Restrict incidence to the range of transpose multiplication. The image is the range of the product of B with its transpose, and the kernel maps isomorphically onto the bicycle subspace. Rank–nullity and equality of transpose ranks give the bicycle dimension. Quotienting the incidence kernel then yields the asserted additive rank identity.

The cycle–cut intersection is the classical bicycle space of Rosenstiehl and Read, On the Principal Edge Tripartition of a Graph, pp. 195–226. Here the rank calculation is paired with the exact row criterion below. https://doi.org/10.1016/S0167-5060(08)70508-9

**Theorem 1.2 (Exact signed rows are feasible precisely when an exact witness has zero class).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedCycleRank.exact_signed_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedCycleRank.exact_signed_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite simple graph, restrict Mathlib incidence to actual unordered edges. The transpose adds the two endpoint labels, so adding its image to the original edge bits performs a vertex switch. The integer incidence weights count negative incident edges, and reduction modulo two is multiplication by the binary incidence matrix. The signed row at each vertex is its degree minus twice its negative count.

Fix a switch whose negative count already has the target parity. Every exact negative-count witness differs from this reference by a cycle. Its residual class vanishes exactly when the cycle is a parity-preserving switch, so a zero-class witness lifts to a vertex switch satisfying the exact signed rows. If the residual dimension is zero, every exact negative-count witness lifts.

For an induced cube example, label vertices by the integers represented by their binary coordinates. Join Hamming-distance-one pairs and use the Huang sign whose negative bit is the parity of the coordinates below the changed coordinate. The induced theta on sites 0, 1, 3, 4, 6, 7, 8, 10 and 11 has three paths of lengths 2, 4 and 4 between sites 0 and 3. Incidence and Laplacian have binary ranks 8 and 6, giving residual rank zero. Enumeration gives 240 distinct exact negative-degree profiles compatible with a switched parity, all attained by switches.

The induced graph on sites 0, 1, 2, 3, 4 and 5 consists of two squares sharing an edge. Incidence and Laplacian both have binary rank 5, giving residual rank two. Enumeration gives 112 exact profiles compatible with a switched parity, of which 32 are attained by switches. These counts enumerate all edge-bit vectors for the exact profiles and all vertex masks for the switched profiles.

For the folded singleton rows of the Q₉ problem, the criterion applies when the graph accounts for the row incidences and the targets account for the other fixed terms. The value of f₂(Q₉) is the question in Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedCycleRank.exact_signed_rows`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedCycleRank.residual_rank_add_twice_rank`
