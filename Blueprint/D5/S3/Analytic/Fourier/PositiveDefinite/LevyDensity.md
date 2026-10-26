# LevyDensity

## Abstract

Positive definite functions and their integral representations.

**Theorem 1.1 (Compound Poisson positivity).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/LevyDensity.finite_density`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/LevyDensity.finite_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an integrable nonnegative real density against a positive measure and a nonnegative rate, the exponential of minus the rate times its integrated cosine deficit is positive definite. A nonnegative cosine mixture, the pointwise exponential series and a positive constant factor establish every finite Gram inequality.

**Theorem 1.2 (Exhaustion by integrable densities).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/LevyDensity.of_truncations`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/LevyDensity.of_truncations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume nonnegative density almost everywhere, measurable truncations which eventually contain almost every point, integrability of the density on every truncation, and integrability of each full cosine deficit. Dominated convergence takes the compound Poisson kernels to the full exponential.

**Theorem 1.3 (Positive half line density criterion).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/LevyDensity.positiveDefinite`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/LevyDensity.positiveDefinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a density D nonnegative on the positive half line, assume D(s)/s is integrable on each interval from 1/(n+1) to n+1 and every cosine deficit times D(s)/s is integrable on the positive half line. For each strictly positive real r, exp of minus 2r times the deficit integral is positive definite. This local integrability formulation specifies exactly the conditions used in truncation and dominated convergence.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/LevyDensity.finite_density`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/LevyDensity.of_truncations`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/LevyDensity.positiveDefinite`
- Dependency: [D5/S3/Analytic/Fourier/PositiveDefinite/Closure](Closure.md)
