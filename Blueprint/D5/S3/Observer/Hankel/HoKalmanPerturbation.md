# HoKalmanPerturbation

## Abstract

Finite noisy Ho-Kalman reconstruction with explicit arithmetic certificates.

**Theorem 1.1 (norm le of row sum le).**

Lean statement: `D5/S3/Observer/Hankel/HoKalmanPerturbation.norm_le_of_row_sum_le`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/HoKalmanPerturbation.norm_le_of_row_sum_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's induced infinity operator norm is bounded by a common row-sum budget, including empty matrix shapes.

**Theorem 1.2 (norm le of entrywise le).**

Lean statement: `D5/S3/Observer/Hankel/HoKalmanPerturbation.norm_le_of_entrywise_le`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/HoKalmanPerturbation.norm_le_of_entrywise_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A uniform entrywise error becomes an operator-norm error multiplied by the number of columns.

**Theorem 1.3 (true det ne zero of inverse margin).**

Lean statement: `D5/S3/Observer/Hankel/HoKalmanPerturbation.true_det_ne_zero_of_inverse_margin`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/HoKalmanPerturbation.true_det_ne_zero_of_inverse_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse of the observed block and a strict perturbation margin force the unknown true block to be nonsingular. The proof uses the existing complete-normed-ring Neumann-series theorem.

**Theorem 1.4 (solve error identity).**

Lean statement: `D5/S3/Observer/Hankel/HoKalmanPerturbation.solve_error_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/HoKalmanPerturbation.solve_error_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distributivity and the two actual matrix equations derive the solve error identity. No perturbation identity is accepted as an independent assumption.

**Theorem 1.5 (solve error le).**

Lean statement: `D5/S3/Observer/Hankel/HoKalmanPerturbation.solve_error_le`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/HoKalmanPerturbation.solve_error_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A scalar inequality absorbs the unknown true-solution norm and yields a posterior error bound in observed quantities and certified noise budgets.

## References

- Truth anchor: `D5/S3/Observer/Hankel/HoKalmanPerturbation.norm_le_of_entrywise_le`
- Truth anchor: `D5/S3/Observer/Hankel/HoKalmanPerturbation.norm_le_of_row_sum_le`
- Truth anchor: `D5/S3/Observer/Hankel/HoKalmanPerturbation.solve_error_identity`
- Truth anchor: `D5/S3/Observer/Hankel/HoKalmanPerturbation.solve_error_le`
- Truth anchor: `D5/S3/Observer/Hankel/HoKalmanPerturbation.true_det_ne_zero_of_inverse_margin`
