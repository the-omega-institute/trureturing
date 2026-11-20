# Absolute convergence in the open right half-plane

## Abstract

The Mellin transform of the complete Mangoldt remainder

**Theorem 1.1 (Transform of the inclusive integrated prime sum).**

$$\forall s \in \mathbb{C},\; 1 < \operatorname{Re}\left(s\right) \Rightarrow \left(\operatorname{IntegrableOn}\left((\lambda y \mapsto \operatorname{exp}\left(-\left(s \cdot y\right)\right) \cdot \operatorname{U}\left(\operatorname{exp}\left(y\right)\right)), \operatorname{Ioi}\left(0\right)\right) \land \int_{0}^{\infty} \operatorname{exp}\left(-\left(s \cdot y\right)\right) \cdot \operatorname{U}\left(\operatorname{exp}\left(y\right)\right) dy = \frac{\frac{-\zeta'\left(s\right)}{\zeta\left(s\right)}}{s \cdot \left(s - 1\right)} - \frac{1}{(s - 1)^{2}} + \frac{1 + \gamma}{s - 1}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtHalfPlane.u_laplace_half_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write x = exp(y). The measure x⁻¹ dx becomes dy, so the Mellin transform of U on x > 1 is the Laplace transform of U(exp(y)) on y > 0. The hypothesis Re(s) > 1 makes the arithmetic series absolutely convergent.

Fix σ = Re(s). Each nonnegative Mangoldt ramp is multiplied by exp(−sy). Its norm equals the ramp multiplied by exp(−σy). Its norm integral thus equals the real part of the individual ramp transform at σ. The convergent von Mangoldt Dirichlet series at σ makes these norm integrals summable. Tonelli gives absolute integrability of the sum, and its complex integral can be computed term by term, yielding (−ζ′(s)/ζ(s))/(s(s−1)).

The logarithmic correction integrates to −1/(s−1)² and the linear correction integrates to (1+γ)/(s−1). In the first moment the boundary term at infinity vanishes because y exp(−(σ−1)y) tends to zero.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtHalfPlane.u_laplace_half_plane`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace](CompleteMangoldtLaplace.md)
