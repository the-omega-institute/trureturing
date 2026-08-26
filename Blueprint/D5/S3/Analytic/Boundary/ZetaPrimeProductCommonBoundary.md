# Zeta Prime-Product Common Boundary

## Abstract

The zeta partition, prime activation product, local entropy, and parameter sensitivity all cross their convergence boundary at one.

**Theorem 1.1 (Five concrete thresholds meet at s equals one).**

$$\begin{aligned}\forall s\in \mathbb{R}, 0 < s \Rightarrow\\\forall p\in \mathbb{P}, q_{p,s} = p^{-s}, \gamma_{p,s} = \operatorname{geometricMeasure}\left(1 - q_{p,s}\right),\\\Gamma_{s} = \operatorname{infinitePi}\left(p\mapsto \gamma_{p,s}\right), H_{p}(s) = -\operatorname{log}\left(1 - q_{p,s}\right) + s \operatorname{log}\left(p\right) \frac{q_{p,s}}{1 - q_{p,s}},\\J_{p}(s) = \frac{\operatorname{log}\left(p\right)^{2} q_{p,s}}{(1 - q_{p,s})^{2}},\\(\operatorname{partitionFunction}\left(s\right) \neq \infty \Leftrightarrow 1 < s) \land\\(\operatorname{Summable}\left(p\mapsto q_{p,s}\right) \Leftrightarrow 1 < s) \land\\(\operatorname{Pr}\left(\Gamma_{s}, FiniteSupportProfiles\right) = 1 \Leftrightarrow 1 < s) \land\\(\operatorname{Summable}\left(p\mapsto H_{p}(s)\right) \Leftrightarrow 1 < s) \land\\(\operatorname{Summable}\left(p\mapsto J_{p}(s)\right) \Leftrightarrow 1 < s).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Boundary/ZetaPrimeProductCommonBoundary.zeta_prime_product_common_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive real parameter s, the zeta partition is the sum of the logarithmic Gibbs weights, while q at prime p is the source activation probability p to the power minus s. The exponent law is the canonical independent product of the corresponding zero-start geometric coordinate laws.

The integer and prime p-series criteria put partition finiteness and activation summability exactly above one. Below and at one, the accepted product theorem gives finite-support profiles measure zero; above one, the first Borel-Cantelli lemma gives them measure one.

The displayed H term is the source geometric-coordinate entropy and the displayed J term is its Fisher sensitivity summand. Lower comparison with prime activation forces divergence through the boundary, while logarithm-weighted p-series bounds give summability above it.

## References

- Truth anchor: `D5/S3/Analytic/Boundary/ZetaPrimeProductCommonBoundary.zeta_prime_product_common_boundary`
- Dependency: [D5/S3/Analytic/PrimeProducts/FiniteMarginalGlobalSupportContrast](../PrimeProducts/FiniteMarginalGlobalSupportContrast.md)
