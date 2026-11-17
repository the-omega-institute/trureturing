# Real matrix variance trees

## Abstract

Real positive-definite matrix weights admit a square-remainder variance identity and a positive-semidefinite defect.

**Theorem 1.1 (The family defect is a square remainder).**

Lean statement: `D5/S3/Quantum/MatrixVarianceTreeReal.family_defect_eq_square`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/MatrixVarianceTreeReal.family_defect_eq_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty finite family of real positive-definite matrix weights and response matrices, the aggregate defect equals the sum of the centered square remainders. The center is the inverse aggregate weight multiplied by the aggregate response; every inverse and adjoint is the actual matrix operation in the Lean statement.

**Theorem 1.2 (The family defect is positive semidefinite).**

Lean statement: `D5/S3/Quantum/MatrixVarianceTreeReal.family_defect_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/MatrixVarianceTreeReal.family_defect_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same finite positive-definite hypotheses, the family defect is positive semidefinite. This follows from the square-remainder identity and the sum of conjugate-transpose quadratic forms, and supplies the positive matrix variance certificate used by the companion tree definitions.

## References

- Truth anchor: `D5/S3/Quantum/MatrixVarianceTreeReal.family_defect_eq_square`
- Truth anchor: `D5/S3/Quantum/MatrixVarianceTreeReal.family_defect_posSemidef`
