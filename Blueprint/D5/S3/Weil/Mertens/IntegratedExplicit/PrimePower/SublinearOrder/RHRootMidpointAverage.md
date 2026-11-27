# A two-term estimate at the midpoint

## Abstract

The midpoint error of the exponential root average

**Theorem 1.1 (Uniform midpoint estimate and signed origin bound).**

$$\mathit{RH} \Rightarrow \left(\forall r \in \mathbb{R},\; 1 < r \Rightarrow \left(\exists C \in \mathbb{R},\; 0 < C \land \left(\forall L \in \mathbb{R},\; \left(0 < L \land L \le \frac{1}{4}\right) \Rightarrow \left(\left(\forall u \in \mathbb{R},\; \left|\operatorname{M}\left(r, u, L\right)\right| \le \operatorname{G}\left(r, L\right) + \operatorname{E}\left(C, L\right)\right) \land \operatorname{G}\left(r, L\right) - \operatorname{E}\left(C, L\right) \le \operatorname{M}\left(r, 0 - \frac{L}{2}, L\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootMidpointAverage.root_signal_exponential_midpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be the centered root spectrum with every actual zero occurrence. For s(r)=1/2−1/(2r), let M(r,u,L) be the average of S(r,u+t) on [0,L] with density proportional to exp(−s(r)t), minus S(r,u+L/2). Put c=(Euler's constant−1+log(2π))/2. The profile G(r,L) is L/(8s(r)) times log(1/L)+log(2r)−2c+1/2, and E(C,L)=C L²(1+log(1/L))².

Pairing points equidistant from the midpoint expresses the flat average error as the integral of the symmetric difference on [0,L/2] divided by L. Integrating the logarithmic profile gives the 1/2 in G. The uniform symmetric bound controls its magnitude for every start, and the signed origin cusp supplies the lower bound at start −L/2.

The two normalized densities have equal mass, so their difference can be integrated against the spectrum after subtracting its midpoint value. The uniform first-difference estimate then bounds the effect of exponential weighting.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootMidpointAverage.root_signal_exponential_midpoint`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffShrinkingRate](RHMobiusEvenCutoffShrinkingRate.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootTailModulus](RHRootTailModulus.md)
