# Actual Paired Function Metric

## Abstract

Actual Paired Function Metric

Put mu0=log(2)^2/4, gamma=pi/4 and kappa0=mu0/(1+gamma^2+mu0). An exact two-by-two sum of squares proves the pointwise function estimate using the actual mean lower bound.

For every c>=3 and arbitrary complex polynomials A,B, kappa0 times the integral on [-1,1] of norm(A(t))^2+norm(B(t))^2 is at most pairedEnergy(c,A,B). Reflection joins the two halves of the integral. This is an integral function metric estimate; it uses no monomial/Hilbert coefficient conversion and has no nonzero-vector premise.

**Definition 1.1 (mu0).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualFunctionMetric.mu0`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualFunctionMetric.mu0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def mu0 : ℝ := (Real.log (2:ℝ))^2/4.

**Definition 1.2 (gamma).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualFunctionMetric.gamma`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualFunctionMetric.gamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def gamma : ℝ := Real.pi/4.

**Definition 1.3 (kappa0).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualFunctionMetric.kappa0`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualFunctionMetric.kappa0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def kappa0 : ℝ := mu0/(1+gamma^2+mu0).

**Theorem 1.4 (actual paired function metric).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualFunctionMetric.actual_paired_function_metric`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualFunctionMetric.actual_paired_function_metric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: theorem actual_paired_function_metric {c : ℕ} (hc : 3 ≤ c) (A B : ℂ[X]) : kappa0*(∫ t in (-1:ℝ)..1, (‖value A t‖^2+‖value B t‖^2)) ≤ pairedEnergy c A B.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFunctionMetric.actual_paired_function_metric`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFunctionMetric.gamma`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFunctionMetric.kappa0`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFunctionMetric.mu0`
- Dependency: [D5/S3/Weil/ZetaBridge/ActualPairedReciprocal](ActualPairedReciprocal.md)
