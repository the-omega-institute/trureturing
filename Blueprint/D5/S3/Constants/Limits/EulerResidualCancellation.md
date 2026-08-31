# Euler Residual Cancellation

## Abstract

The Euler-Mascheroni constant cancels the harmonic-logarithmic residual.

**Theorem 1.1 (The harmonic-logarithmic Euler residual vanishes).**

$$\lim_{n\to\infty} (H_n - \log n - \gamma) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Limits/EulerResidualCancellation.harmonic_log_euler_residual_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib proves that the harmonic numbers minus log n converge to the Euler-Mascheroni constant.

Subtracting that constant from the convergent sequence subtracts it from the limit, leaving zero.

## References

- Truth anchor: `D5/S3/Constants/Limits/EulerResidualCancellation.harmonic_log_euler_residual_tendsto_zero`
