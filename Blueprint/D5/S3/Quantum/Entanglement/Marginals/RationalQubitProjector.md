# Joint qubit states from rational quadratic witnesses

## Abstract

A rational rank-two qubit completion from a quadratic-form witness.

**Theorem 1.1 (A rank-two completion for two prescribed Bloch marginals).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/RationalQubitProjector.rational_rank_two_of_quadratic_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/RationalQubitProjector.rational_rank_two_of_quadratic_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take rational three-vectors a and b with squared lengths satisfying |a|² < |b|². Let y and v be rational three-vectors with y nonzero. Suppose a · y = b · v and |y|² = (1 − |b|²)|v|² + (b · v)². Then the two trace-one Bloch matrices for a and b are the partial traces of a positive semidefinite joint matrix with rational coordinates and rank exactly two.

The quadratic equation forces v to be nonzero. Divide y by |v|² to get u. Set k = b − (a · u)v and split a into its components parallel and perpendicular to u. The witness equations give k · v = 0 and |k|² + |u|²|v|² = 1. The corresponding sum of Pauli tensor terms is a traceless Hermitian involution. Its positive eigenspace has dimension two.

On this eigenspace the two components of a determine a Hermitian correction. Its square is a scalar times the identity and the scalar is less than one by the squared-length comparison. The identity plus the correction is positive definite, so the compression has rank two. One partial trace recovers both components of a. The other recovers b as the sum of k and (a · u)v.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/RationalQubitProjector.rational_rank_two_of_quadratic_witness`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment](../AbsolutePPT/ContractionAttainment.md)
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/FibRationalPureExtension](FibRationalPureExtension.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Measurement/FourQubitParentConstruction](../../Measurement/FourQubitParentConstruction.md)
