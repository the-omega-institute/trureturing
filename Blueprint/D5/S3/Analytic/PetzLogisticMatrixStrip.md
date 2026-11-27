# Matrix logistic boundary comparison

## Abstract

The full logistic comparison for finite Frobenius matrix curves and their physical boundary pairs.

**Theorem 1.1 (Exact energy with a prescribed cross term).**

Lean statement: `D5/S3/Analytic/PetzLogisticMatrixStrip.full_logistic_of_boundary_cross`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticMatrixStrip.full_logistic_of_boundary_cross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a bounded matrix curve continuous on the closed strip and holomorphic inside. Suppose two matrix residuals have the same trace cross term as the analytic boundary values. Assume the lower residual square is integrable against both weights and the upper residual square is integrable against the upper weight. The weighted boundary sum minus the logistic squared difference equals the lower residual square with the difference weight plus twice the analytic midline square integral.

**Theorem 1.2 (Finite spectral sums are entire).**

Lean statement: `D5/S3/Analytic/PetzLogisticMatrixStrip.differentiable_exp_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticMatrixStrip.differentiable_exp_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite matrix-valued sum of complex exponentials with real frequencies is complex differentiable everywhere.

**Theorem 1.3 (Uniform bound on finite spectral sums).**

Lean statement: `D5/S3/Analytic/PetzLogisticMatrixStrip.norm_exp_sum_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticMatrixStrip.norm_exp_sum_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the absolute real part of the argument is at most a, the Frobenius norm is bounded by the sum of coefficient norms weighted by exp(a times the absolute frequency).

**Theorem 1.4 (Preservation by two unitary multipliers).**

Lean statement: `D5/S3/Analytic/PetzLogisticMatrixStrip.sq_norm_mul_unitaries`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticMatrixStrip.sq_norm_mul_unitaries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the left matrix has adjoint times itself equal to the identity and the right matrix has itself times its adjoint equal to the identity, multiplying on both sides preserves the Frobenius norm squared.

**Definition 1.5 (Analytic residual).**

Lean statement: `D5/S3/Analytic/PetzLogisticMatrixStrip.residual`

*Formalization.* `D5/S3/Analytic/PetzLogisticMatrixStrip.residual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The analytic residual is R(1/2) minus S(z) O(z) R(1/2 − z).

**Definition 1.6 (Common physical amplitude).**

Lean statement: `D5/S3/Analytic/PetzLogisticMatrixStrip.commonAmplitude`

*Formalization.* `D5/S3/Analytic/PetzLogisticMatrixStrip.commonAmplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The common amplitude is S(−it) R(1/2 + it).

**Definition 1.7 (Lower physical amplitude).**

Lean statement: `D5/S3/Analytic/PetzLogisticMatrixStrip.lowerAmplitude`

*Formalization.* `D5/S3/Analytic/PetzLogisticMatrixStrip.lowerAmplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lower amplitude is O(it) R(1/2).

**Definition 1.8 (Upper physical amplitude).**

Lean statement: `D5/S3/Analytic/PetzLogisticMatrixStrip.upperAmplitude`

*Formalization.* `D5/S3/Analytic/PetzLogisticMatrixStrip.upperAmplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The upper amplitude is S(1/2) O(1/2 + it).

**Theorem 1.9 (Faithful boundary norms).**

Lean statement: `D5/S3/Analytic/PetzLogisticMatrixStrip.boundary_norms`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticMatrixStrip.boundary_norms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For unital source and reference power laws compatible with adjoints, the same two unitary multipliers convert both analytic boundaries to their corresponding physical residuals. The two individual squares and the square of their difference agree.

**Theorem 1.10 (Cross term on singular input supports).**

Lean statement: `D5/S3/Analytic/PetzLogisticMatrixStrip.supported_boundary_cross`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzLogisticMatrixStrip.supported_boundary_cross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For multiplicative power laws compatible with adjoints and S(0) R(1/2) = R(1/2), the trace pairing of the two physical residuals equals the trace pairing of the analytic boundaries. The lower residual already has source right support and the upper residual has reference left support.

## References

- Truth anchor: `D5/S3/Analytic/PetzLogisticMatrixStrip.boundary_norms`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMatrixStrip.commonAmplitude`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMatrixStrip.differentiable_exp_sum`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMatrixStrip.full_logistic_of_boundary_cross`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMatrixStrip.lowerAmplitude`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMatrixStrip.norm_exp_sum_le`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMatrixStrip.residual`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMatrixStrip.sq_norm_mul_unitaries`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMatrixStrip.supported_boundary_cross`
- Truth anchor: `D5/S3/Analytic/PetzLogisticMatrixStrip.upperAmplitude`
- Dependency: [D5/S3/Analytic/PetzLogisticMidline](PetzLogisticMidline.md)
