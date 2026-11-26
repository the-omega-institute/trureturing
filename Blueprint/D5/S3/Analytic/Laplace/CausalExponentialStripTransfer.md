# Causal exponential strip transfer

## Abstract

Transfer of square integrability from a Fourier section to a causal function.

**Definition 1.1 (Causal exponential kernel).**

Lean statement: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.kernel`

*Formalization.* `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.kernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real c, a, and s, the kernel is c exp(−as) for s ≥ 0 and zero for s < 0, with values included in the complex numbers.

**Definition 1.2 (Fourier multiplier).**

Lean statement: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.multiplier`

*Formalization.* `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.multiplier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real c, a, and ξ, the multiplier is c/(a + 2πiξ).

**Definition 1.3 (Causal smoothing).**

Lean statement: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.smoothing`

*Formalization.* `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.smoothing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real c and complex-valued g on the real line, smoothing is convolution of g with the causal kernel of amplitude and rate c.

**Definition 1.4 (Exponential tilt).**

Lean statement: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.tilt`

*Formalization.* `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.tilt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real d and complex-valued g on the real line, the tilt at time t is exp(−dt) g(t).

**Definition 1.5 (Normalized vertical section).**

Lean statement: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.sectionAt`

*Formalization.* `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.sectionAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a complex-valued function F on ℂ and real a and ξ, the section at a evaluated at ξ is F(a + 2πiξ).

**Theorem 1.6 (Transform of the kernel).**

Lean statement: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.fourier_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.fourier_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real amplitude c, positive rate a, and real frequency ξ, the Fourier transform of the causal kernel at ξ is c/(a + 2πiξ).

**Theorem 1.7 (Absolute integrability of the old-line convolution).**

Lean statement: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.integrable_oldLine_integrand`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.integrable_oldLine_integrand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c ≥ 0, a > 0, and integrable g₀, the function s ↦ kernel(c, a, s) g₀(t − s) is integrable for each real t.

**Theorem 1.8 (Pointwise inversion on the old line).**

Lean statement: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.oldLineSmoothing_eq_fourierInv`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.oldLineSmoothing_eq_fourierInv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c ≥ 0 and a > 0, assume g₀ is integrable and its Fourier transform times the multiplier c/(a + 2πiξ) is integrable. The convolution of the causal kernel with g₀ equals the inverse Fourier transform of that product as a function.

**Theorem 1.9 (Absolute integrability with a bounded past).**

Lean statement: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.integrable_smoothing_integrand`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.integrable_smoothing_integrand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c > 0 and let g be measurable. If |g(x)| ≤ M for every x ≤ t, then s ↦ kernel(c, c, s) g(t − s) is integrable.

**Theorem 1.10 (Convergence at continuity points).**

Lean statement: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.smoothing_tendsto_atTop`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.smoothing_tendsto_atTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If g is measurable, continuous at t, and satisfies |g(x)| ≤ M for all x ≤ t, its causal exponential smoothing at t tends to g(t) as c tends to positive infinity.

**Theorem 1.11 (Transfer at a fixed rate).**

Lean statement: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.smoothing_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.smoothing_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let σ < σ₀, C ≥ 0, and p > 0. Assume F is complex differentiable at every point of the closed strip [σ, σ₀] and |F(a + iy)| ≤ C(1 + |y|)^(−p) for every a in [σ, σ₀] and real y. Assume the tilt of g by σ₀ − σ is integrable and its Fourier transform equals the section of F at σ₀ as a function. Assume the section at σ belongs to L². For each c > 0, the smoothing of g equals the pointwise inverse Fourier transform of the target section multiplied by c/(c + 2πiξ). The smoothing belongs to L² and its extended L² norm is bounded by that of the target section.

**Theorem 1.12 (L² membership after removing the smoothing).**

Lean statement: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.memLp_of_strip_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.memLp_of_strip_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let σ < σ₀, C ≥ 0, and p > 0. Assume F is complex differentiable at every point of the closed strip [σ, σ₀] and |F(a + iy)| ≤ C(1 + |y|)^(−p) for every a in [σ, σ₀] and real y. Assume the tilt of g by σ₀ − σ is integrable and its Fourier transform equals the section of F at σ₀ as a function. Assume the section at σ belongs to L². Suppose further that g is measurable, continuous almost everywhere, vanishes at negative times, and is bounded on each interval [0, T]. Then g belongs to L². The smoothing converges almost everywhere along the positive integer rates, and the fixed-rate L² bound passes to the limit.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.fourier_kernel`
- Truth anchor: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.integrable_oldLine_integrand`
- Truth anchor: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.integrable_smoothing_integrand`
- Truth anchor: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.kernel`
- Truth anchor: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.memLp_of_strip_transfer`
- Truth anchor: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.multiplier`
- Truth anchor: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.oldLineSmoothing_eq_fourierInv`
- Truth anchor: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.sectionAt`
- Truth anchor: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.smoothing`
- Truth anchor: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.smoothing_tendsto_atTop`
- Truth anchor: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.smoothing_transfer`
- Truth anchor: `D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.tilt`
- Dependency: [D5/S3/Analytic/Laplace/ExponentialMultiplierFourier](ExponentialMultiplierFourier.md)
