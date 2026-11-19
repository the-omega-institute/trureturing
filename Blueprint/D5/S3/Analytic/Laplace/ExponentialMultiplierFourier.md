# Fourier inversion with an exponential multiplier

## Abstract

The exponential multiplier in the normalized inverse Fourier transform.

**Definition 1.1 (Target-line multiplier).**

Lean statement: `D5/S3/Analytic/Laplace/ExponentialMultiplierFourier.targetMultiplier`

*Formalization.* `D5/S3/Analytic/Laplace/ExponentialMultiplierFourier.targetMultiplier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real c and ξ, the target-line multiplier is c/(c + 2πiξ).

**Theorem 1.2 (L² contraction of the pointwise inverse).**

Lean statement: `D5/S3/Analytic/Laplace/ExponentialMultiplierFourier.targetInverse_memLp`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/ExponentialMultiplierFourier.targetInverse_memLp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c > 0 and let f be a complex-valued L² function on the real line. If the product of f and the target-line multiplier is integrable, its pointwise inverse Fourier transform belongs to L² and has extended L² norm at most that of f.

**Theorem 1.3 (Normalization of the target-line integral).**

Lean statement: `D5/S3/Analytic/Laplace/ExponentialMultiplierFourier.targetInverse_eq_vertical_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/ExponentialMultiplierFourier.targetInverse_eq_vertical_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real σ, c, t and any complex function F, evaluate the inverse Fourier transform of ξ ↦ F(σ + 2πiξ) c/(c + 2πiξ) at t. It equals the integral of the smoothed integrand along σ + iy with respect to real y, scaled by 1/(2π). Both integrals use Lean's total Bochner integral.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/ExponentialMultiplierFourier.targetInverse_eq_vertical_integral`
- Truth anchor: `D5/S3/Analytic/Laplace/ExponentialMultiplierFourier.targetInverse_memLp`
- Truth anchor: `D5/S3/Analytic/Laplace/ExponentialMultiplierFourier.targetMultiplier`
- Dependency: [D5/S3/Analytic/Laplace/ExponentialMultiplierContour](ExponentialMultiplierContour.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/LineFourier](../../Weil/ZetaGamma/FormCore/LineFourier.md)
