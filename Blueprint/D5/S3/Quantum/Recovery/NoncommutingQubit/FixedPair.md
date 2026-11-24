# Noncommuting qubit fixed pairs

## Abstract

Rigidity and tensor factorization from a recovered pair of noncommuting qubit states.

**Theorem 1.1 (Rigidity of a noncommuting fixed pair).**

Lean statement: `D5/S3/Quantum/Recovery/NoncommutingQubit/FixedPair.cptp_eq_id_of_noncommuting_fixed_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/NoncommutingQubit/FixedPair.cptp_eq_id_of_noncommuting_fixed_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

Let a completely positive trace-preserving map on complex two by two matrices fix two positive semidefinite trace-one matrices A and B with AB different from BA. The map equals the identity on the whole complex matrix algebra.

Diagonalize the nonzero traceless Hermitian difference A minus B by a unitary. In this basis the map fixes the difference of the two rank-one coordinate projections. Their images have trace one and nonnegative diagonal entries. The fixed difference forces the weight on each opposite eigenline to vanish. Each such weight is a sum of squared Kraus entries, so both off-diagonal entries of every Kraus matrix vanish.

Diagonal Kraus matrices act by entrywise scalar multiplication. Trace preservation gives diagonal multipliers equal to one. A must have a nonzero off-diagonal entry in this basis, since otherwise B would also be diagonal. Fixing A and using Hermiticity forces both other multipliers to be one.

**Theorem 1.2 (Physical tensor form from two recovery equations).**

Lean statement: `D5/S3/Quantum/Recovery/NoncommutingQubit/FixedPair.tensor_form_of_noncommuting_qubit_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/NoncommutingQubit/FixedPair.tensor_form_of_noncommuting_qubit_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

Let Phi be a completely positive trace-preserving map from any finite complex matrix algebra to the qubit algebra. A completely positive trace-preserving recovery R restores two density matrices S and T from their noncommuting outputs. Suppose S is positive definite. Then Phi composed with R equals the identity on every qubit matrix.

Use the represented Kraus families in the pointwise tensor theorem. Its support projection acts as the identity on R(Phi(S)) and hence equals the identity, because S is invertible. The resulting tensor isometry U is therefore unitary onto the whole physical input space. The environment operator kappa is positive definite and has trace one. For every qubit matrix Z, the recovery is U(kappa tensor Z)U*. In particular the two recovery equations identify both input states with products using the same kappa.

Let Q be R of the qubit identity. The Kraus left-inverse relations give Q times the trace adjoint of Phi at Z equal to R(Z). The support calculation makes Q invertible. In the tensor coordinates, Q is U(kappa tensor identity)U*, so the trace adjoint of Phi at Z is U(identity tensor Z)U*. Pairing with every Z gives the physical partial trace over the environment.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/NoncommutingQubit/FixedPair.cptp_eq_id_of_noncommuting_fixed_pair`
- Truth anchor: `D5/S3/Quantum/Recovery/NoncommutingQubit/FixedPair.tensor_form_of_noncommuting_qubit_recovery`
- Dependency: [D5/S3/Quantum/FixedPointProjection](../../FixedPointProjection.md)
- Dependency: [D5/S3/Quantum/Recovery/ActualChannelAlgebra](../ActualChannelAlgebra.md)
