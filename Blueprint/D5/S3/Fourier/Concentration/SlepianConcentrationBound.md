# Slepian Concentration Bound

## Abstract

The maximal eigenvalue of a positive Slepian concentration spectrum is bounded by one and by the trace budget.

**Theorem 1.1 (The maximal concentration rate is at most one and the trace).**

$$\begin{aligned}\forall \lambda: \mathbb{N} \to \mathbb{R}, L, m, Lambda\in\mathbb{R},\\0 \leq L \land 0 \leq m \land\\(\forall j\in\mathbb{N}, 0 \leq \lambda\left(j\right) \leq 1) \land \operatorname{Summable}\left(\lambda\right) \land\\\sum_{j=0}^{\infty} \lambda\left(j\right) = \frac{L m}{\pi} \land (\exists j\in\mathbb{N}, Lambda = \lambda\left(j\right)) \Rightarrow\\Lambda \leq \operatorname{min}\left(1, \frac{L m}{\pi}\right) \land\\(L m = 0 \Rightarrow Lambda = 0).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/SlepianConcentrationBound.slepian_concentration_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let lambda be a nonnegative summable concentration spectrum, with every eigenvalue at most one. Its sum is the Slepian trace Lm/pi, and the maximum Lambda is assumed to be attained by one spectral mode.

The singleton finite sum is bounded by the total sum via Mathlib's Summable.sum_le_tsum. Hence the attained eigenvalue is at most the trace, while the pointwise contraction bound makes it at most one.

If Lm is zero, pi is nonzero and the trace is zero. Nonnegativity then squeezes the attained maximum to zero, supplying the boundary equality rather than only a one-sided estimate. The operator-theoretic trace and spectral facts are explicit hypotheses because pinned Mathlib has no suitable trace-class API.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/SlepianConcentrationBound.slepian_concentration_bound`
