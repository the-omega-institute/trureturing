# Joint circuit torsion for ordered direct sums

## Abstract

The transpose cokernel of joint circuit restriction factors over ordered direct sums.

**Theorem 1.1 (The transpose cokernel of a direct sum).**

Lean statement: `D5/S3/Combinatorics/Matroids/DirectSumCircuitTorsion.joint_circuit_transpose_cokernel_tensor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/DirectSumCircuitTorsion.joint_circuit_transpose_cokernel_tensor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M and N be matroids on a finite linearly ordered carrier. Their grounds are disjoint, and every ground vertex of M precedes every ground vertex of N. The source lattice is the lattice of integral augmented top cycles. The joint target contains one contraction cycle lattice for each circuit. The joint map records all signed aggregate restrictions.

The ordered join induces an integral linear equivalence from the tensor product of the source lattices to the source lattice of the direct sum. Under the dual equivalence, a pure tensor of functionals evaluates on a joined pair as the product of the evaluations. Sending the tensor of two quotient classes to the class of the corresponding tensor functional gives an isomorphism onto the transpose cokernel of the direct sum.

A basis and every allowable one-element exchange split over the two grounds. The ordered join takes pairs of normalized passive cycles to normalized passive cycles of the sum. Every circuit lies in one factor and contraction leaves the other factor unchanged. The signed readout on a left circuit factors without an extra sign. A right circuit has the sign from passing its facet across the left face. These signs are units, so the transpose relations are the sum of the two tensor extensions of the factor relation submodules.

**Theorem 1.2 (The rank-one transpose cokernel).**

Lean statement: `D5/S3/Combinatorics/Matroids/DirectSumCircuitTorsion.rank_one_transpose_cokernel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/DirectSumCircuitTorsion.rank_one_transpose_cokernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty ground of size n whose bases are precisely the ground singletons, the transpose cokernel is the cyclic integer module of order n. A circuit is a pair and its contraction has the empty basis. The corresponding readout is a signed difference of singleton coefficients. Hence all singleton evaluations represent the same generator in the cokernel, and the augmented boundary makes n times that generator vanish. A cycle with coefficients one except at a chosen vertex, where the coefficient is one minus n, gives a character sending the generator to one modulo n.

**Theorem 1.3 (Torsion of the integral lifting quotient).**

Lean statement: `D5/S3/Combinatorics/Matroids/DirectSumCircuitTorsion.joint_lifting_obstruction_equiv`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/DirectSumCircuitTorsion.joint_lifting_obstruction_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nonempty ground, the signed pivot pairings give injectivity of joint restriction. The torsion submodule of the integral target modulo the joint image is the saturation of that image modulo the image. Smith coordinates identify this torsion submodule with the transpose cokernel. The identification uses a choice of Smith bases.

**Theorem 1.4 (The cyclic obstruction for two rank-one factors).**

Lean statement: `D5/S3/Combinatorics/Matroids/DirectSumCircuitTorsion.rank_one_sum_joint_lifting_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/DirectSumCircuitTorsion.rank_one_sum_joint_lifting_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an ordered direct sum of two nonempty rank-one loopless matroids with ground sizes m and n, the obstruction to an integral joint lift of a rationally compatible integral tuple is cyclic of order gcd(m,n). The tensor of the two cyclic generators generates the tensor of the transpose cokernels. Bezout's identity gives its annihilator and the tensor of the reductions modulo gcd(m,n) detects its exact order. In particular, coprime ground sizes give a saturated joint image.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/DirectSumCircuitTorsion.joint_circuit_transpose_cokernel_tensor`
- Truth anchor: `D5/S3/Combinatorics/Matroids/DirectSumCircuitTorsion.joint_lifting_obstruction_equiv`
- Truth anchor: `D5/S3/Combinatorics/Matroids/DirectSumCircuitTorsion.rank_one_sum_joint_lifting_obstruction`
- Truth anchor: `D5/S3/Combinatorics/Matroids/DirectSumCircuitTorsion.rank_one_transpose_cokernel`
- Dependency: [D5/S3/Combinatorics/Matroids/JointCircuitGramCertificate](JointCircuitGramCertificate.md)
