# Spectral primitives at the endpoints

## Abstract

The prime-window remainder under RH

**Definition 1.1 (Primitive on the product of circles).**

$$\forall h \in \mathbb{T}^{\mathbb{N}},\; \operatorname{P}\left(h\right) = \Re (\sum_{k \in \mathbb{N}} \frac{c_{k} \cdot h_{k}}{i \cdot \gamma_{k}})$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowRemainder.spectralPrimitive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each index k refers to an actual nontrivial zero occurrence ρₖ. Write cₖ=1/(ρₖ(1−ρₖ)) and γₖ=Im ρₖ. The ordinate bound |γₖ|>10 dominates each primitive term by |cₖ|/10 on the entire product. The resulting uniformly convergent series has continuous real part P.

**Definition 1.2 (Centered prime-only window mass).**

$$\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \operatorname{E}\left(a, B\right) = \operatorname{N}\left(a, B\right) - 2 \cdot \operatorname{log}\left(\frac{B}{a}\right)$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowRemainder.windowDiscrepancy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

Write Qϑ(x) for the prime-only tail, the integral of (ϑ(u)−u)/u² over u>x from Zhao's equation (14). The window mass N(a,B) is the integral of max(−Qϑ(x),0)/√x from a to B.

**Definition 1.3 (Constant for a fixed left cutoff).**

$$\forall a \in \mathbb{R},\; \operatorname{C}\left(a\right) = \int_{\operatorname{log}\left(a\right)}^{\infty} \operatorname{e}\left(y\right) dy - \operatorname{P}\left(\operatorname{phi}\left(\operatorname{log}\left(a\right)\right)\right)$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowRemainder.fixedCutoffConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let φ(t) have coordinates exp(iγₖt). The function e is the log-coordinate density max(√(exp y)(−Qϑ(exp y)),0) minus 2 and the real part of the normalized zero series. Under RH that series is Σₖ cₖφ(y)ₖ, and e is absolutely integrable above log 2.

**Theorem 1.4 (Uniform remainder, cluster interval and exact window identity).**

$$RH \Rightarrow \left(\left(\forall epsilon \in \mathbb{R},\; 0 < epsilon \Rightarrow \left(\exists X \in \mathbb{R},\; 2 \le X \land \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; X \le a \Rightarrow \left(a \le B \Rightarrow \left|\operatorname{E}\left(a, B\right) - \operatorname{P}\left(\operatorname{phi}\left(\operatorname{log}\left(B\right)\right)\right) + \operatorname{P}\left(\operatorname{phi}\left(\operatorname{log}\left(a\right)\right)\right)\right| < epsilon\right)\right)\right)\right) \land \left(\left(\forall a \in \mathbb{R},\; 2 \le a \Rightarrow \left(\operatorname{K}\left(a\right) = \operatorname{C}\left(a\right) + \operatorname{P}\left(H\right) \land \left(\exists l \in \mathbb{R},\; \exists u \in \mathbb{R},\; l < u \land \operatorname{K}\left(a\right) = [l, u]\right)\right)\right) \land \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; 2 \le a \Rightarrow \left(a \le B \Rightarrow \operatorname{E}\left(a, B\right) - \operatorname{P}\left(\operatorname{phi}\left(\operatorname{log}\left(B\right)\right)\right) + \operatorname{P}\left(\operatorname{phi}\left(\operatorname{log}\left(a\right)\right)\right) = \int_{\operatorname{log}\left(a\right)}^{\operatorname{log}\left(B\right)} \operatorname{e}\left(y\right) dy\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowRemainder.prime_window_remainder_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

Write H for the closure of the real orbit φ, and K(a) for the set of real cluster values of E(a,B) as B tends to infinity. The translated image C(a)+P(H) consists of all C(a)+P(h) with h in H.

Under RH each zero frequency equals iγₖ. Integrate the normalized series term by term over the logarithmic window using the summable majorant |cₖ|. The two endpoint series give P(φ(log B))−P(φ(log a)). The residual is exactly the integral of e on the same window, bounded in absolute value by the integral of |e| over (log a,∞).

For fixed a the residual converges to the integral of e over (log a,∞). Forward recurrence gives all phases in H, and compactness makes the translated image closed. The image is connected because the real orbit is continuous. At time zero the normalized series has positive real part given by the first Li mass. Integrating over a short interval shows that P takes distinct values on the orbit.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowRemainder.fixedCutoffConstant`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowRemainder.prime_window_remainder_of_rh`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowRemainder.spectralPrimitive`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowRemainder.windowDiscrepancy`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster](PrimePhaseCluster.md)
