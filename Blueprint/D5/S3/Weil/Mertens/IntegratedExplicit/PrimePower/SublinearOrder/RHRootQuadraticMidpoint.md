# Pairing the weighted modes

## Abstract

The quadratic midpoint remainder of the exponential root average

**Theorem 1.1 (Uniform midpoint estimate and signed origin bound).**

$$\mathit{RH} \Rightarrow \left(\forall r \in \mathbb{R},\; 1 < r \Rightarrow \left(\exists C \in \mathbb{R},\; 0 < C \land \left(\forall L \in \mathbb{R},\; \left(0 < L \land L \le \frac{1}{4}\right) \Rightarrow \left(\left(\forall u \in \mathbb{R},\; \left|\operatorname{M}\left(r, u, L\right)\right| \le \operatorname{G}\left(r, L\right) + \operatorname{E}\left(C, L\right)\right) \land \operatorname{G}\left(r, L\right) - \operatorname{E}\left(C, L\right) \le \operatorname{M}\left(r, 0 - \frac{L}{2}, L\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuadraticMidpoint.root_signal_exponential_midpoint_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be the centered root spectrum with every actual zero occurrence. For s(r)=1/2−1/(2r), let M(r,u,L) be the average of S(r,u+t) on [0,L] with density proportional to exp(−s(r)t), minus S(r,u+L/2). Put c=(Euler's constant−1+log(2π))/2. The profile G(r,L) is L/(8s(r)) times log(1/L)+log(2r)−2c+1/2, and E(C,L)=C L².

For frequency ω and half-displacement h, put q=1−cos(ωh). The half-pair multiplier is −cosh(sh)q−i sinh(sh)sin(ωh). Its squared norm is q²+2q sinh²(sh), so its norm is at most q+sinh²(sh). The sum of the q terms is bounded by the full cosine kernel, and the sum of the frequency-independent terms is bounded by the absolute coefficient mass times sinh²(sh). This controls every starting point.

At center zero, the paired integrand is the symmetric increment times cosh(sh) minus the odd increment times sinh(sh). The symmetric cusp and the linear odd-increment bound give the signed lower comparison. The centered denominator is the integral of 2 cosh(sh) on [0,L/2], which differs from L by at most L³ on the stated range. Integrating the cusp profile gives the 1/2 in G.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuadraticMidpoint.root_signal_exponential_midpoint_quadratic`
- Dependency: [D5/S3/Analytic/Asymptotics/CommonPhaseSpectralCurvature](../../../../../Analytic/Asymptotics/CommonPhaseSpectralCurvature.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootMidpointAverage](RHRootMidpointAverage.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHSignedShrinkingLower](RHSignedShrinkingLower.md)
