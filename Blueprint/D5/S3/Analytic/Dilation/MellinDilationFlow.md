# Mellin Transform on the Dilation Flow

## Abstract

Mellin is Fourier in logarithmic time along the dilation flow.

**Theorem 1.1 (Mellin is Fourier in logarithmic time).**

$$\forall f:\mathbb{R} \to \mathbb{C}, \forall s\in \mathbb{C}, \operatorname{mellin}(f,s) = \int_{\mathbb{R}}\exp(i \operatorname{Im}(s)t) \cdot \exp(\Re(s)t) \cdot f(\exp(t))\,dt.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Dilation/MellinDilationFlow.mellin_eq_fourier_on_dilation_flow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set x = exp(t), so dx contributes exp(t). The original Mellin factor x^(s-1) combines with that Jacobian to give exp(s t). Splitting the complex exponential exposes exp(Re(s)t) as the dilation weight and exp(i Im(s)t) as its Fourier phase.

Pinned Mathlib already proves the stronger bridge `mellin_eq_fourier` in the reflected coordinate u = -t. The Lean proof reuses that theorem and Fourier reflection to obtain the displayed t = log(x) orientation; it does not reprove change of variables.

The identity is unconditional because Mathlib totalizes nonintegrable Bochner integrals. A checked compact nonzero window witnesses MellinConvergent at s = 1 and makes the displayed integrand equal one at logarithmic time zero.

## References

- Truth anchor: `D5/S3/Analytic/Dilation/MellinDilationFlow.mellin_eq_fourier_on_dilation_flow`
