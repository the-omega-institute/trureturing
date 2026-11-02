# Covariance metrics for rectangular matrices

## Abstract

Rectangular completion of the square and the attained positive-metric Riccati trace minimum used by the Audenaert covariance route.

**Theorem 1.1 (Rectangular metric completion).**

Lean statement: `D5/S3/Quantum/Matrix/CovarianceMetric.rectangular_metric_square`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CovarianceMetric.rectangular_metric_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite index types m and k, a positive definite square metric D and arbitrary rectangular A,C satisfy the exact ordered identity A* D A + C* D inverse C - A* C - C* A = (A - D inverse C)* D (A - D inverse C). The right side is positive semidefinite. The rectangular factors may be singular or zero; only D is required to be positive definite.

**Theorem 1.2 (Rectangular trace bound).**

Lean statement: `D5/S3/Quantum/Matrix/CovarianceMetric.rectangular_metric_trace_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CovarianceMetric.rectangular_metric_trace_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the real trace of the positive semidefinite remainder and using conjugate-transpose trace symmetry gives 2 Re Tr(A* C) <= Re Tr(A* D A) + Re Tr(C* D inverse C). The finite matrix statement includes zero-dimensional and singular rectangular-factor cases.

**Theorem 1.3 (Positive-metric Riccati remainder).**

Lean statement: `D5/S3/Quantum/Matrix/CovarianceMetric.metric_square`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CovarianceMetric.metric_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Hermitian G and positive definite D, D + G D inverse G - G - G equals (D-G) D inverse (D-G), and this remainder is positive semidefinite. Positivity of D is the exact condition used for the actual inverse.

**Theorem 1.4 (Covariance-metric gap).**

Lean statement: `D5/S3/Quantum/Matrix/CovarianceMetric.covariance_metric_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CovarianceMetric.covariance_metric_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite P,S,D, let G be the existing geometric mean of P inverse and S. Then GPG=S and the difference between the trace cost at D and the cost at G is exactly the real trace of the positive Riccati remainder multiplied by P, hence is nonnegative.

**Theorem 1.5 (Attained positive-metric minimum).**

Lean statement: `D5/S3/Quantum/Matrix/CovarianceMetric.covariance_metric_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CovarianceMetric.covariance_metric_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite P and S, the same G is an attained global minimizer over every positive definite competitor D of Re Tr(DP) + Re Tr(D inverse S), with value twice Re Tr(GP). The statement makes no claim about singular-metric inversion or singular minimizers.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CovarianceMetric.covariance_metric_gap`
- Truth anchor: `D5/S3/Quantum/Matrix/CovarianceMetric.covariance_metric_minimum`
- Truth anchor: `D5/S3/Quantum/Matrix/CovarianceMetric.metric_square`
- Truth anchor: `D5/S3/Quantum/Matrix/CovarianceMetric.rectangular_metric_square`
- Truth anchor: `D5/S3/Quantum/Matrix/CovarianceMetric.rectangular_metric_trace_bound`
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound](LinGProperty/GeometricMeanBound.md)
