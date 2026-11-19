# Exponential multiplier contour shift

## Abstract

Vertical contour shifting under polynomial decay after exponential smoothing.

**Definition 1.1 (Smoothed inversion integrand).**

Lean statement: `D5/S3/Analytic/Laplace/ExponentialMultiplierContour.smoothed`

*Formalization.* `D5/S3/Analytic/Laplace/ExponentialMultiplierContour.smoothed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real σ, c, t, a complex function F, and a complex point z, the integrand is exp((z − σ)t) F(z) c/(c + z − σ).

**Theorem 1.2 (Absolute convergence and vertical shift).**

Lean statement: `D5/S3/Analytic/Laplace/ExponentialMultiplierContour.smoothed_vertical_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/ExponentialMultiplierContour.smoothed_vertical_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let σ < σ₀, c > 0, C ≥ 0, and p > 0. Assume F is complex differentiable at every point of the closed strip with real parts in [σ, σ₀], and that |F(a + iy)| ≤ C(1 + |y|)^(−p) for every a in [σ, σ₀] and real y. For each real t, every vertical section of the smoothed integrand on the strip is integrable in y. Its integral in a from σ to σ₀ tends to zero as y tends to either positive or negative infinity. The full integrals in y on the two boundary lines are equal.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/ExponentialMultiplierContour.smoothed`
- Truth anchor: `D5/S3/Analytic/Laplace/ExponentialMultiplierContour.smoothed_vertical_shift`
