# Point Potentials and Cyclic Factors

## Abstract

The integral joint lifting obstruction of a rank-three sparse-paving matroid with singleton parallel classes.

**Definition 1.1 (Normalized point potentials).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.IsOmissionPotential`

*Formalization.* `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.IsOmissionPotential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A potential vanishes at the chosen anchor, has zero total sum, and is killed by three at every point. It takes equal values at the ends of every pair in no omitted triple. Its values on each omitted triple sum to zero.

**Theorem 1.2 (Reduced matrix for the integral obstruction).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.rank_three_lifting_obstruction_equiv_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.rank_three_lifting_obstruction_equiv_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the bases on a finite ordered ground set of size n greater than three are all triples except a specified family whose distinct members meet in at most one point. For singleton parallel classes and any distinct root and anchor, the integral lifting obstruction is linearly equivalent over the integers to the kernel of the reduced omitted-triangle matrix modulo n. Each column is an increasing pair avoiding the root and anchor. The row of a triple evaluates the alternating form on two differences from the first point of the triple.

**Theorem 1.3 (Torsion count at any divisor).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.rank_three_lifting_obstruction_torsion_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.rank_three_lifting_obstruction_torsion_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses, index the omitted triples without repetition and let m be their number. Put b equal to the number of pairs avoiding the root and anchor. For each positive divisor q of n, the number of elements killed by q, multiplied by q to the power m, equals q to the power b times the number of normalized potentials with values modulo the greatest common divisor of q and three. The signed rows identify the transpose kernel with point-potential differences, and the finite character pairing relates the sizes of the primal and transpose kernels.

**Theorem 1.4 (Cyclic factors for all rank-three omission families).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.rank_three_lifting_obstruction_cyclic_factors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.rank_three_lifting_obstruction_cyclic_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m distinct omitted triples under the intersection bound, put b equal to the binomial coefficient counting pairs of the n minus two points outside the root and anchor. The integral lifting obstruction is linearly equivalent over the integers to b minus m cyclic factors of order n and d cyclic factors of order three. The normalized potentials with values modulo the greatest common divisor of n and three number exactly three to the power d. Smith normal form splits the unconstrained residue coordinates from the remaining finite module. The torsion counts at n and its greatest common divisor with three show that this latter module is killed by three.

**Theorem 1.5 (Cyclic factors of the twelve affine-line omissions).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.affine_plane_lifting_obstruction_cyclic_factors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.affine_plane_lifting_obstruction_cyclic_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the nine points of the affine plane of order three, omit its twelve lines and keep all other triples as bases. The normalized potentials are the linear forms in the two affine coordinates. Their two independent slopes give nine potentials. The integral obstruction therefore has nine cyclic factors of order nine and two cyclic factors of order three.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.IsOmissionPotential`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.affine_plane_lifting_obstruction_cyclic_factors`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.rank_three_lifting_obstruction_cyclic_factors`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.rank_three_lifting_obstruction_equiv_kernel`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.rank_three_lifting_obstruction_torsion_card`
- Dependency: [D5/S3/Combinatorics/Matroids/CircuitDifferenceBasis](CircuitDifferenceBasis.md)
- Dependency: [D5/S3/Combinatorics/Matroids/RankTwoCircuitInvariantFactors](RankTwoCircuitInvariantFactors.md)
- Dependency: [D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates](SparsePavingCircuitCoordinates.md)
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitResidueDiagonal](UniformCircuitResidueDiagonal.md)
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms](UniformCircuitResidueForms.md)
