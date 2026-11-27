# Weight residues for binary cube adjacency

## Abstract

Weight residues for binary cube adjacency

**Definition 1.1 (Weight of a binary cube function).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/BinaryAdjacencyWeight.weight`

*Formalization.* `D5/S3/Combinatorics/Graph/Hypercube/BinaryAdjacencyWeight.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Hamming weight is the sum of the natural representatives of the binary values, so it counts the vertices where the function is one.

**Theorem 1.2 (Binary adjacency weight modulo four).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/BinaryAdjacencyWeight.weight_adjacency_mod_four`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube/BinaryAdjacencyWeight.weight_adjacency_mod_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In every dimension n, the weight of Bf is congruent to n times the weight of f modulo four. Square the unsigned neighbor count at every vertex. Modulo four the square equals the parity of that count. Each diagonal term sums to the preimage weight by a singleton translation. For distinct directions i and j, translation by their sum is a fixed-point-free involution exchanging the two factors of the correlation. The doubled correlation vanishes modulo four.

**Theorem 1.3 (A coordinate moment gives the image weight residue).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/BinaryAdjacencyWeight.weight_adjacency_mod_four_eq_coordinate_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube/BinaryAdjacencyWeight.weight_adjacency_mod_four_eq_coordinate_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In positive even dimension, each coordinate moment of Bf is the parity of f's weight. Multiplying its natural representative by n modulo four gives the exact weight residue of Bf. For n congruent to two modulo four, residue zero means that every preimage has even weight, and residue two means that every preimage has odd weight.

**Theorem 1.4 (Kernel weights are multiples of four in dimensions divisible by four).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/BinaryAdjacencyWeight.four_dvd_weight_of_adjacency_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube/BinaryAdjacencyWeight.four_dvd_weight_of_adjacency_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* W. Fish, J. D. Key, and E. Mwambene (2009). *Graphs, designs and codes related to the n-cube*. DOI: [10.1016/j.disc.2008.09.024](https://doi.org/10.1016/j.disc.2008.09.024). URL: <https://doi.org/10.1016/j.disc.2008.09.024>.

*Commentary.*

Every binary adjacency kernel word in positive dimension divisible by four has weight divisible by four. Section 4, Result 2 of the cited note's source records self-duality of the positive even-dimensional adjacency code. Here the explicit contraction gives kernel equals image, and the image weight congruence gives the divisibility.

In the Q8 fold of Hong, Wu and Xia's Q9 Problem 2, the syndrome of a support is B applied to its indicator over the binary field. Equal syndromes put the symmetric difference in the kernel. In the 114+144 regular order-17 branch, the 17 dimer centers D cannot have zero syndrome. If D has the same syndrome as a singleton q, the possible weights of D △ {q} are 16 and 18. Divisibility by four forces weight 16, so q belongs to D. In the 120+138 fold, equal-syndrome singleton supports must have symmetric difference of weight divisible by four. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/BinaryAdjacencyWeight.four_dvd_weight_of_adjacency_eq_zero`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/BinaryAdjacencyWeight.weight`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/BinaryAdjacencyWeight.weight_adjacency_mod_four`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/BinaryAdjacencyWeight.weight_adjacency_mod_four_eq_coordinate_moment`
- Dependency: [D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment](BinaryKernelCoordinateMoment.md)
