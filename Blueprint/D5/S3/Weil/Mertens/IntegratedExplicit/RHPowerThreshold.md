# Power normalization of the integrated Mangoldt remainder

## Abstract

The sharp exponent for the integrated Mangoldt remainder under RH

**Theorem 1.1 (The powers giving decay).**

$$RiemannHypothesis \Rightarrow \left(\forall theta \in \mathbb{R},\; \operatorname{Tendsto}\left((\lambda x:\mathbb{R} \mapsto \frac{U\left(x\right)}{x^{theta}}), atTop, \operatorname{nhds}\left(0\right)\right) \Leftrightarrow \frac{1}{2} < theta\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RHPowerThreshold.u_div_rpow_tendsto_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here U is CompleteMertensPeak.U, formed from the complete inclusive Mangoldt sum up to the natural floor of x. The variable x runs over the real axis. For each fixed exponent above one half and each positive tolerance, one cutoff controls every later x, hence every point of every later power window.

Set x = exp(y) and M = firstLiMass. Then U(x)/x^θ equals G(y) exp((1/2 − θ)y). Under RH the absolute value of G is eventually bounded by M + 1. For θ > 1/2 the exponential factor tends to zero, and log(x) tends to infinity with x.

The first Li coefficient gives M > 0. Given any cutoff, the recurrence of G supplies a natural n beyond it with G(n) > M/2. For θ ≤ 1/2 the exponential factor at n is at least one, so the quotient at exp(n) exceeds M/2. This includes θ = 1/2.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RHPowerThreshold.u_div_rpow_tendsto_zero_iff`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope](RHSharpActualEnvelope.md)
