# Prime-power correction and persistence of negative values

## Abstract

Negative-part windows of the Chebyshev tail

**Theorem 1.1 (Prime-power correction and negative-part window bound).**

$$\operatorname{Tendsto}\left((\lambda x \mapsto \operatorname{sqrt}\left(x\right) \cdot \operatorname{D}\left(x\right)), atTop, \operatorname{nhds}\left(2\right)\right) \land \left(\forall C \in \mathbb{R},\; \left(\forall t \in \mathbb{R},\; 1 \le t \Rightarrow \psi\left(t\right) - \theta\left(t\right) \le C \cdot \operatorname{sqrt}\left(t\right)\right) \Rightarrow \left(\left(\forall x \in \mathbb{R},\; 1 \le x \Rightarrow \left(0 \le \operatorname{D}\left(x\right) \land \operatorname{D}\left(x\right) \le \frac{2 \cdot C}{\operatorname{sqrt}\left(x\right)}\right)\right) \land \left(\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \left(1 \le a \land a \le b\right) \Rightarrow \left(0 \le \operatorname{W}\left(a, b\right) \land \operatorname{W}\left(a, b\right) \le 2 \cdot C \cdot \operatorname{log}\left(\frac{b}{a}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection.prime_power_window_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For α equal to the prime-power function ψ or the prime-only function ϑ, let Qα(x) be the absolutely convergent integral of (α(t)−t)/t² from x ≥ 1 to infinity. Write D(x)=Qψ(x)−Qϑ(x). For 1 ≤ a ≤ b, let W(a,b) be the integral from a to b of [max(−Qϑ(x),0)−max(−Qψ(x),0)]/√x. All variables are real.

For every x ≥ 1, subtracting the two tails expresses D(x) as the integral of the nonnegative kernel (ψ(t)−ϑ(t))/t². The prime number theorem gives (ψ(t)−ϑ(t))/√t → 1. For any ε > 0 the ratio lies within ε of one at every sufficiently large t, so for every sufficiently large x the entire tail lies between (1−ε) and (1+ε) times the integral of t to the power −3/2. That integral equals 2/√x.

A Chebyshev bound ψ(t)−ϑ(t) ≤ C√t exists unconditionally. Negative parts reverse order and are 1-Lipschitz, so the window integrand is between zero and 2C/x. In particular b=a to the power 3/2 costs at most C log a.

**Theorem 1.2 (A negative interior value forces window mass).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall r \in \mathbb{R},\; \left(\left(1 \le a \land a \le (1 - r) \cdot x\right) \land \left((1+r) \cdot x \le b \land \left(\left(0 < r \land r \le \frac{1}{2}\right) \land \operatorname{Q}\left(x\right) \le 0 - 4 \cdot r^{2}\right)\right)\right) \Rightarrow r^{3} \cdot \operatorname{sqrt}\left(x\right) \le \operatorname{N}\left(a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection.prime_tail_negative_window_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the displayed statement Q is the prime-only tail Qϑ. Write N(a,b) for the integral of max(−Qϑ(z),0)/√z over [a,b]. The hypothesis on the window leaves a relative margin r on both sides of x.

Monotonicity of ϑ bounds the increment Qϑ(z)−Qϑ(x) by log(z/x)+ϑ(x)(1/z−1/x). This integral comparison holds at prime jumps. Choose z on the left when ϑ(x)≤x and on the right when ϑ(x)≥x. On the chosen side the upper bound is at most log(z/x)+x/z−1. Using log(t)≤t−1 bounds it by (z−x)²/(zx), at most 2r².

The negative part is therefore at least 2r² throughout a subinterval of length rx, where √z≤2√x. Integrating gives r³√x. A budget strictly below r³√x excludes the asserted depth at that interior point. The estimate requires a given window and gives no existence result for small-budget windows.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection.prime_power_window_correction`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection.prime_tail_negative_window_lower`
- Dependency: [D5/S3/Arith/Robin/CompleteMertensPeak](../../../Arith/Robin/CompleteMertensPeak.md)
- Dependency: [D5/S3/Arith/Robin/EulerLayerRootCorrection](../../../Arith/Robin/EulerLayerRootCorrection.md)
- Dependency: [D5/S3/Weil/Mertens/WeightedPrimeLimit](../WeightedPrimeLimit.md)
