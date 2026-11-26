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

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/DirectSumCircuitTorsion.joint_circuit_transpose_cokernel_tensor`
- Dependency: [D5/S3/Combinatorics/Matroids/JointCircuitGramCertificate](JointCircuitGramCertificate.md)
