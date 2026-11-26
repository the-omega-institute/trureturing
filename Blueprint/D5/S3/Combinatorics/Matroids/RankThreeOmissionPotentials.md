# Point Potentials and Cyclic Factors

## Abstract

Take a finite ordered ground set of n greater than three points with singleton parallel classes. The bases are all triples except for m omitted triples, any two of which meet in at most one point.

**Theorem 1.1 (Torsion count at any divisor).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.rank_three_lifting_obstruction_torsion_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.rank_three_lifting_obstruction_torsion_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Index the omitted triples without repetition, let m be their number, and choose any anchor. Put b equal to the binomial coefficient counting pairs from n minus two points. For each positive divisor q of n, the number of elements killed by q, multiplied by q to the power m, equals q to the power b times the number of normalized potentials with values modulo the greatest common divisor of q and three. The signed rows identify the transpose kernel with point-potential differences, and the finite character pairing relates the sizes of the primal and transpose kernels.

**Theorem 1.2 (Cyclic factors for all rank-three omission families).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.rank_three_lifting_obstruction_cyclic_factors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.rank_three_lifting_obstruction_cyclic_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m distinct omitted triples under the intersection bound, choose any anchor for the potentials. Put b equal to the binomial coefficient counting pairs from n minus two points. The integral lifting obstruction is linearly equivalent over the integers to b minus m cyclic factors of order n and d cyclic factors of order three. The normalized potentials with values modulo the greatest common divisor of n and three number exactly three to the power d. Smith normal form splits the unconstrained residue coordinates from the remaining finite module. The torsion counts at n and its greatest common divisor with three show that this latter module is killed by three.

**Theorem 1.3 (Cyclic factors of the twelve affine-line omissions).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.affine_plane_lifting_obstruction_cyclic_factors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.affine_plane_lifting_obstruction_cyclic_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the nine points of the affine plane of order three, omit its twelve lines and keep all other triples as bases. The normalized potentials are the linear forms in the two affine coordinates. Their two independent slopes give nine potentials. The integral obstruction therefore has nine cyclic factors of order nine and two cyclic factors of order three.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.affine_plane_lifting_obstruction_cyclic_factors`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.rank_three_lifting_obstruction_cyclic_factors`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials.rank_three_lifting_obstruction_torsion_card`
- Dependency: [D5/S3/Combinatorics/Matroids/RankThreeOmissionCoordinates](RankThreeOmissionCoordinates.md)
