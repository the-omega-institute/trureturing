# Gaussian cutoff kernels

## Abstract

Smooth frequency cutoffs and real inverse Fourier kernels.

**Theorem 1.1 (Nonnegative cutoff).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianCutoff.chi_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianCutoff.chi_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product of the two smooth transition factors is nonnegative for every real parameter and frequency.

**Theorem 1.2 (Cutoff bounded by one).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianCutoff.chi_le_one`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianCutoff.chi_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each transition factor lies between zero and one, so their product is at most one.

**Theorem 1.3 (Even cutoff).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianCutoff.chi_even`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianCutoff.chi_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Replacing the frequency by its negative exchanges the two transition factors and leaves the cutoff unchanged.

**Theorem 1.4 (Central plateau).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianCutoff.chi_eq_one`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianCutoff.chi_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive M, the cutoff equals one whenever the absolute frequency is at most M.

**Theorem 1.5 (Outer vanishing).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianCutoff.chi_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianCutoff.chi_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive M, the cutoff vanishes whenever the absolute frequency is at least M plus M to the one-quarter power.

**Theorem 1.6 (Smooth cutoff).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianCutoff.chi_contDiff`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianCutoff.chi_contDiff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cutoff is infinitely differentiable because its factors are smooth transitions composed with affine functions.

**Theorem 1.7 (Smooth multiplier).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_multiplier_contDiff`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_multiplier_contDiff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product of the cutoff and exp(t squared divided by twice M squared) is infinitely differentiable.

**Theorem 1.8 (Compact frequency support).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_multiplier_hasCompactSupport`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_multiplier_hasCompactSupport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive M, the multiplier has compact support contained in [-(M+Delta), M+Delta], where Delta is M to the one-quarter power.

**Theorem 1.9 (Even multiplier).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_multiplier_even`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_multiplier_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both the Gaussian factor and the cutoff are even, so the multiplier is even.

**Theorem 1.10 (Real Schwartz kernel).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_kernelSchwartz_coe`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_kernelSchwartz_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse Fourier transform of the normalized multiplier is a complex Schwartz function with zero imaginary part. Its value is the complexification of the real cutoff kernel. The normalized multiplier at xi is b evaluated at two pi times xi.

**Theorem 1.11 (Integrable kernel).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_kernel_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_kernel_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real cutoff kernel is integrable for every M. For positive M it is the real part of a Schwartz function, and for nonpositive M it is zero.

**Theorem 1.12 (Cosine convolution identity).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_kernel_cos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_kernel_cos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For M at least one, convolution of the cutoff kernel with cos(gamma y) multiplies it by exp(gamma squared divided by twice M squared) times the cutoff at gamma. Fourier inversion with the normalization b(two pi xi) supplies the identity for every real gamma and y.

**Theorem 1.13 (Uniform Fourier multiplier bound).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_multiplier_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_multiplier_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For M at least one, the norm of the Mathlib Fourier transform of the complexified real kernel is at most exp(2) at every real frequency. Its transform is b(two pi xi), supported where the absolute angular frequency is at most M plus M to the one-quarter power.

**Theorem 1.14 (Uniform bounds on transition derivatives).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianCutoff.smoothTransition_derivatives_bounded`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianCutoff.smoothTransition_derivatives_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative integer n, the absolute value of the nth derivative of the fixed smooth transition has a finite positive bound on the whole real line. Positive-order derivatives vanish outside the unit interval, and continuity bounds them on that interval.

**Theorem 1.15 (Uniform kernel tail).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_kernel_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_kernel_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists a positive constant C independent of M such that, for every M at least one, the integral of the absolute cutoff kernel over absolute v at least one is at most C divided by M. Five differentiations give a multiplier derivative integral bounded by C divided by M: the central region contributes order M to the minus fourth power, and the two transition bands contribute order Delta to the minus fourth power. The Fourier derivative identity then gives fifth-power decay in v, whose tail is integrable.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/GaussianCutoff.chi_contDiff`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianCutoff.chi_eq_one`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianCutoff.chi_eq_zero`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianCutoff.chi_even`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianCutoff.chi_le_one`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianCutoff.chi_nonneg`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_kernelSchwartz_coe`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_kernel_cos`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_kernel_integrable`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_kernel_tail`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_multiplier_bound`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_multiplier_contDiff`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_multiplier_even`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianCutoff.cutoff_multiplier_hasCompactSupport`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianCutoff.smoothTransition_derivatives_bounded`
