# A negative defect at every odd order at least five.

## Abstract

A negative defect at every odd order at least five.

**Theorem 1.1 (Exact even Pauli defects).**

Lean statement: `D5/S3/Quantum/Matrix/TaylorMajorization/Pauli.defect_even`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TaylorMajorization/Pauli.defect_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m at least one, the Pauli pair Z=diag(1,-1) and X with off-diagonal entries one has defect at order 2m equal to 4 to the m minus 2 to the m+1. Order zero has defect zero. The product moments follow from Z squared and X squared equal to I; a scalar binomial expansion computes the trace of Q. Anticommutation gives (Z+X) squared equal to 2I.

**Theorem 1.2 (Vanishing odd Pauli defects).**

Lean statement: `D5/S3/Quantum/Matrix/TaylorMajorization/Pauli.defect_odd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TaylorMajorization/Pauli.defect_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every odd order 2m+1 the unshifted Pauli defect is zero. The binomial trace formula for Q has opposite signed powers, and (Z+X) to an odd power is a scalar multiple of the traceless matrix Z+X.

**Theorem 1.3 (Strictly negative defects after translation).**

Lean statement: `D5/S3/Quantum/Matrix/TaylorMajorization/Pauli.defect_shift_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TaylorMajorization/Pauli.defect_shift_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every odd natural k at least five and every positive real t, the defect for Z-tI and X is strictly negative. In the binomial translation sum, odd defects vanish. Every even defect is nonnegative, and its coefficient has negative sign because k is odd. The order-four term is strictly negative since choose(k,4) and t to the k-4 are positive.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/TaylorMajorization/Pauli.defect_even`
- Truth anchor: `D5/S3/Quantum/Matrix/TaylorMajorization/Pauli.defect_odd`
- Truth anchor: `D5/S3/Quantum/Matrix/TaylorMajorization/Pauli.defect_shift_negative`
- Dependency: [D5/S3/Quantum/Matrix/TaylorMajorization/Shift](Shift.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
