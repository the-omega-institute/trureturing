# Coordinate moments and the binary adjacency kernel of a cube

## Abstract

Coordinate moments and the binary adjacency kernel of a cube

Fish, Key and Mwambene record that the binary adjacency row code of a positive even-dimensional cube is self-dual and has minimum weight equal to the dimension in Graphs, designs and codes related to the n-cube, Discrete Mathematics 309 (2009), 3255–3269, Result 2, crediting Fish and Key–Seneviratne. Lemma 2(1) gives the binary square identity in every dimension. https://doi.org/10.1016/j.disc.2008.09.024

**Definition 1.1 (Binary cube adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.adjacency`

*Formalization.* `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.adjacency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A cube vertex x is a subset of Fin n. The operator B takes a function f with values in ZMod 2 to the function whose value at x is the sum of f over the n singleton flips of x.

**Definition 1.2 (Coordinate bit).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.coordinateBit`

*Formalization.* `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.coordinateBit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For i in Fin n, the coordinate bit bᵢ(x) is one if i belongs to x and zero otherwise, with values in ZMod 2.

**Theorem 1.3 (Each coordinate moment recovers the parity of the preimage).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.coordinate_moment_adjacency`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.coordinate_moment_adjacency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For even n, i in Fin n and every binary function f on the cube, the sum over x of bᵢ(x)(Bf)(x) equals the sum over x of f(x). Reindexing by each singleton flip turns the coefficient of f(x) into the sum of bᵢ over the shell at x. An even number of copies of bᵢ(x) cancel and the flip in direction i adds one.

In the 114+144 branch of Hong, Wu and Xia's Q9 Problem 2, the axial 17+2 fold leaves a Q8 with 17 majority dimer sites in the order-17 contact block. For a critical block with unit contact Gram 4I + A and primitive positive integral Perron vector a satisfying Aa = 4a, the contact rows exhaust the signed Huang image norm. Let D be the dimer sites at which a is odd. Reducing the image modulo two gives the indicator of a contact subset U with 1_U = B1_D.

For each of the eight axes, the number of U sites with that coordinate equal to one is congruent to |D| modulo two. Both halves have that parity because |U| is even, as each dimer shell has eight vertices. In the weight-16 filter, the half sizes therefore test the parity class of a proposed shell preimage directly from U. For a regular order-17 block, all 17 Perron entries are one, so every coordinate split of U has two odd half sizes. This is a necessary condition in the fold analysis for Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

**Definition 1.4 (Coordinate contraction).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.coordinateContraction`

*Formalization.* `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.coordinateContraction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For i in Fin n, Hᵢ multiplies a binary cube function by bᵢ and pulls the product back along the singleton flip in direction i.

**Theorem 1.5 (The adjacency and contraction identity).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.adjacency_coordinateContraction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.adjacency_coordinateContraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In any dimension with i in Fin n, BHᵢf + HᵢBf = f for every binary cube function f. The flips commute, and paired terms cancel in every direction except i, where the two coordinate bits sum to one.

**Theorem 1.6 (Binary adjacency squares to zero in even dimension).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.adjacency_adjacency_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.adjacency_adjacency_eq_zero` (`✓ std3`). ∎

*Citation.* W. Fish, J. D. Key, and E. Mwambene (2009). *Graphs, designs and codes related to the n-cube*. DOI: [10.1016/j.disc.2008.09.024](https://doi.org/10.1016/j.disc.2008.09.024). URL: <https://doi.org/10.1016/j.disc.2008.09.024>.

*Commentary.*

For even n and every binary cube function f, B(Bf) = 0. Swapping the ordered pair of flip directions pairs off the terms with distinct indices. Commutation makes the two terms equal, so their sum vanishes in characteristic two. The diagonal contributes n copies of f, which also vanish.

**Theorem 1.7 (Full neighbor shells span the kernel).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.adjacency_eq_zero_iff_exists_adjacency`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.adjacency_eq_zero_iff_exists_adjacency` (`✓ std3`). ∎

*Citation.* W. Fish, J. D. Key, and E. Mwambene (2009). *Graphs, designs and codes related to the n-cube*. DOI: [10.1016/j.disc.2008.09.024](https://doi.org/10.1016/j.disc.2008.09.024). URL: <https://doi.org/10.1016/j.disc.2008.09.024>.

*Commentary.*

For even n, a chosen i in Fin n and every binary cube function f, Bf = 0 if and only if Bg = f for some binary cube function g. For a kernel word the contraction identity gives g = Hᵢf, and the converse follows from the square-zero identity.

The image of the point indicator at c is the full shell of c, consisting of all its singleton flips. Expand g as a sum of its point indicators, so Bg is the binary sum of the full shells whose centers have g(c) = 1. In support language this sum is symmetric difference. When f is supported on one cube parity, Hᵢf is supported on the opposite parity, so the same construction gives shell generators for the kernel on each parity.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.adjacency`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.adjacency_adjacency_eq_zero`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.adjacency_coordinateContraction`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.adjacency_eq_zero_iff_exists_adjacency`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.coordinateBit`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.coordinateContraction`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCoordinateMoment.coordinate_moment_adjacency`
