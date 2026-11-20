# The square-root correction to the prime-only tail

## Abstract

Removing prime powers from a critical Chebyshev window

**Theorem 1.1 (Prime-power correction and negative-part window bound).**

$$\operatorname{Tendsto}\left((\lambda x \mapsto \operatorname{sqrt}\left(x\right) \cdot \operatorname{D}\left(x\right)), atTop, \operatorname{nhds}\left(2\right)\right) \land \left(\forall C \in \mathbb{R},\; \left(\forall t \in \mathbb{R},\; 1 \le t \Rightarrow \psi\left(t\right) - \theta\left(t\right) \le C \cdot \operatorname{sqrt}\left(t\right)\right) \Rightarrow \left(\left(\forall x \in \mathbb{R},\; 1 \le x \Rightarrow \left(0 \le \operatorname{D}\left(x\right) \land \operatorname{D}\left(x\right) \le \frac{2 \cdot C}{\operatorname{sqrt}\left(x\right)}\right)\right) \land \left(\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \left(1 \le a \land a \le b\right) \Rightarrow \left(0 \le \operatorname{W}\left(a, b\right) \land \operatorname{W}\left(a, b\right) \le 2 \cdot C \cdot \operatorname{log}\left(\frac{b}{a}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection.prime_power_window_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For α equal to the prime-power function ψ or the prime-only function ϑ, let Qα(x) be the absolutely convergent integral of (α(t)−t)/t² from x ≥ 1 to infinity. Write D(x)=Qψ(x)−Qϑ(x). For 1 ≤ a ≤ b, let W(a,b) be the integral from a to b of [max(−Qϑ(x),0)−max(−Qψ(x),0)]/√x. All variables are real.

For every x ≥ 1, subtracting the two tails expresses D(x) as the integral of the nonnegative kernel (ψ(t)−ϑ(t))/t². The prime number theorem gives (ψ(t)−ϑ(t))/√t → 1. For any ε > 0 the ratio lies within ε of one at every sufficiently large t, so for every sufficiently large x the entire tail lies between (1−ε) and (1+ε) times the integral of t to the power −3/2. That integral equals 2/√x.

A Chebyshev bound ψ(t)−ϑ(t) ≤ C√t exists unconditionally. Negative parts reverse order and are 1-Lipschitz, so the window integrand is between zero and 2C/x. In particular b=a to the power 3/2 costs at most C log a.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection.prime_power_window_correction`
- Dependency: [D5/S3/Arith/Robin/CompleteMertensPeak](../../../Arith/Robin/CompleteMertensPeak.md)
- Dependency: [D5/S3/Arith/Robin/EulerLayerRootCorrection](../../../Arith/Robin/EulerLayerRootCorrection.md)
- Dependency: [D5/S3/Weil/Mertens/WeightedPrimeLimit](../WeightedPrimeLimit.md)
