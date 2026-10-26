# Positive definite functions

## Abstract

Closure of positive definite translation kernels.

**Theorem 1.1 (Nonnegative scalar multiples).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.smul`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by a nonnegative real scalar preserves every finite complex Gram inequality.

**Theorem 1.2 (Finite sums).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.sum`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite sum of translation kernels with positive semidefinite Gram matrices again has positive semidefinite Gram matrices.

**Theorem 1.3 (Pointwise products).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.mul`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Schur product theorem applies to the two Gram matrices on the same finite point family.

**Theorem 1.4 (Real dilations).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.dilation`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.dilation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Replacing every point x by a times x proves closure for every real a, including zero and negative values.

**Theorem 1.5 (Pointwise limits).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.limit`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed cone of positive semidefinite matrices contains the entrywise limit along every nontrivial filter.

**Theorem 1.6 (Unitary characters).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.character`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.character` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The character exp(i s t) gives a rank one complex Gram matrix for each real frequency s.

**Theorem 1.7 (Cosine kernels).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.cos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.cos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cosine is the average of the characters with opposite frequencies.

**Theorem 1.8 (Nonnegative constants).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.const`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonnegative constant is a nonnegative multiple of the frequency zero character.

**Theorem 1.9 (Natural powers).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.pow`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Repeated Schur products prove closure under natural pointwise powers. This assertion does not concern general real powers.

**Theorem 1.10 (Pointwise exponentials).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.exp`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential series consists of Schur powers with nonnegative factorial coefficients; finite partial sums and pointwise convergence give positivity.

**Theorem 1.11 (Positive measure integrals).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.integral`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the parameter family is positive definite almost everywhere and each point evaluation is integrable against the positive measure. Conjugation and finite Gram sums commute with the integral; every complex quadratic form remains nonnegative.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.character`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.const`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.cos`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.dilation`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.exp`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.integral`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.limit`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.mul`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.pow`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.smul`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/Closure.sum`
- Dependency: [D5/S3/Weil/Probability/FiniteGaussianSchoenberg](../../../Weil/Probability/FiniteGaussianSchoenberg.md)
- Dependency: [D5/S3/Weil/ZetaLinear/FiniteInversePoissonCriterion](../../../Weil/ZetaLinear/FiniteInversePoissonCriterion.md)
