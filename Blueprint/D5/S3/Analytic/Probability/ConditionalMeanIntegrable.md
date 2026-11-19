# Equal quantile bins for integrable real laws

## Abstract

Conditional means on equal quantile bins approximate integrable real probability laws in convex order.

For a real probability law rho, Mean is its identity integral and IntegrableIdentity asserts its finite absolute first moment. StopLoss(rho,z) is the integral of max(x-z,0). Upper(rho,t) and Lower(rho,t) integrate the generalized quantile against Lebesgue measure on (t,1] and (0,t], respectively.

**Theorem 1.1 (Upper integrated quantiles under stop-loss order).**

$$\begin{aligned}\forall mu,nu: \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \operatorname{IntegrableIdentity}\left(mu\right) \Rightarrow\operatorname{IntegrableIdentity}\left(nu\right) \Rightarrow\\(\forall z: \mathbb{R}, \operatorname{StopLoss}\left(mu, z\right) \leq \operatorname{StopLoss}\left(nu, z\right)) \Rightarrow\\\forall t \in (0,1], \operatorname{Upper}\left(mu, t\right) \leq \operatorname{Upper}\left(nu, t\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ConditionalMeanIntegrable.upperIntegratedQuantile_le_of_stopLoss_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Compare at the stop-loss threshold given by the right quantile. At an interior level this threshold attains the bound for the right law. At level one both upper integrals vanish.

**Theorem 1.2 (Lower quantile integrals from equal means).**

$$\begin{aligned}\forall mu,nu: \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \operatorname{IntegrableIdentity}\left(mu\right) \Rightarrow\operatorname{IntegrableIdentity}\left(nu\right) \Rightarrow\\\operatorname{Mean}\left(mu\right) = \operatorname{Mean}\left(nu\right) \Rightarrow\forall t \in (0,1], \\\operatorname{Upper}\left(mu, t\right) \leq \operatorname{Upper}\left(nu, t\right) \Rightarrow\operatorname{Lower}\left(nu, t\right) \leq \operatorname{Lower}\left(mu, t\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ConditionalMeanIntegrable.lowerIntegratedQuantile_ge_of_upper_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Split the integral of each quantile at the given level. The total quantile integral equals the original mean, so subtracting the upper integral gives the reverse inequality on the lower interval.

For a positive integer n, BinIntegrable(rho,n) asserts Lebesgue integrability of the quantile of rho on every bin (k/n,(k+1)/n] with k in Fin n. BinMean is n times that integral. PrefixSum sums the bin means through and including index K, and Lower integrates the same quantile over (0,t] at level t.

**Lemma 1.3 (Quantile integrability on every bin).**

$$\forall mu: \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \operatorname{IntegrableIdentity}\left(mu\right) \Rightarrow\forall n: \mathbb{N}, 0<n \Rightarrow\operatorname{BinIntegrable}\left(mu, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ConditionalMeanIntegrable.integrableOn_quantile_bin_of_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The quantile on (0,1] is integrable by the original law and its finite absolute first moment. Restrict to each quantile bin.

**Theorem 1.4 (Monotonicity of integrable quantile-bin means).**

$$\forall mu: \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \forall n: \mathbb{N}, 0<n \Rightarrow\operatorname{BinIntegrable}\left(mu, n\right) \Rightarrow\operatorname{Monotone}\left(k\mapsto\operatorname{BinMean}\left(mu, n, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ConditionalMeanIntegrable.condMeanAtom_monotone_of_integrable_bins` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

For two ordered bins, values of the quantile on the earlier bin are bounded above by values on the later bin almost everywhere. The bins have equal mass and their quantile integrals are finite.

**Theorem 1.5 (Prefix sums of integrable quantile-bin means).**

$$\begin{aligned}\forall mu: \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \forall n: \mathbb{N}, 0<n \Rightarrow\operatorname{BinIntegrable}\left(mu, n\right) \Rightarrow\\\forall K: \operatorname{Fin}\left(n\right), \operatorname{PrefixSum}\left(mu, n, K\right) = n \cdot \operatorname{Lower}\left(mu, (K+1)/n\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ConditionalMeanIntegrable.condMeanAtomize_partial_sum_eq_of_integrable_bins` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The first K+1 right-closed bins form a disjoint union up to their final endpoint. Finite additivity of the integral sums their means, with the same scaling factor n on every bin.

BinLaw is the uniform finite law of the bin means. WeakLimit uses its embedding into probability measures. ConvexOrder compares the expectations of every convex real test for the two finite laws.

**Theorem 1.6 (Weak convergence of integrable bin-mean laws).**

$$\begin{aligned}\forall mu: \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), (\forall n: \mathbb{N}, 0<n \Rightarrow\operatorname{BinIntegrable}\left(mu, n\right)) \Rightarrow\\\operatorname{WeakLimit}\left(n \mapsto \operatorname{BinLaw}\left(mu, n+1\right), mu\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ConditionalMeanIntegrable.condMeanAtomize_tendsto_of_integrable_bins` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

At an interior continuity point of the quantile, the bin containing the point shrinks to it. The bin means converge there, and the exceptional set has measure zero. Bounded continuous tests give dominated convergence for the probability laws.

**Theorem 1.7 (Convex order of the equiweighted bin-mean laws).**

$$\begin{aligned}\forall mu,nu: \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \operatorname{IntegrableIdentity}\left(mu\right) \Rightarrow\operatorname{IntegrableIdentity}\left(nu\right) \Rightarrow\\\operatorname{Mean}\left(mu\right) = \operatorname{Mean}\left(nu\right) \Rightarrow\forall n: \mathbb{N}, 0<n \Rightarrow\\(\forall t \in (0,1], \operatorname{Lower}\left(nu, t\right) \leq \operatorname{Lower}\left(mu, t\right)) \Rightarrow\\\operatorname{ConvexOrder}\left(\operatorname{BinLaw}\left(mu, n\right), \operatorname{BinLaw}\left(nu, n\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ConditionalMeanIntegrable.condMeanAtomize_convexOrder_of_lowerIntegratedQuantile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Both vectors of bin means are increasing and have equal total sums. The lower quantile integrals order their prefix sums at each bin endpoint. Finite majorization compares the expectations of every convex test.

## References

- Truth anchor: `D5/S3/Analytic/Probability/ConditionalMeanIntegrable.condMeanAtom_monotone_of_integrable_bins`
- Truth anchor: `D5/S3/Analytic/Probability/ConditionalMeanIntegrable.condMeanAtomize_convexOrder_of_lowerIntegratedQuantile`
- Truth anchor: `D5/S3/Analytic/Probability/ConditionalMeanIntegrable.condMeanAtomize_partial_sum_eq_of_integrable_bins`
- Truth anchor: `D5/S3/Analytic/Probability/ConditionalMeanIntegrable.condMeanAtomize_tendsto_of_integrable_bins`
- Truth anchor: `D5/S3/Analytic/Probability/ConditionalMeanIntegrable.integrableOn_quantile_bin_of_integrable`
- Truth anchor: `D5/S3/Analytic/Probability/ConditionalMeanIntegrable.lowerIntegratedQuantile_ge_of_upper_le`
- Truth anchor: `D5/S3/Analytic/Probability/ConditionalMeanIntegrable.upperIntegratedQuantile_le_of_stopLoss_le`
- Dependency: [D5/S3/Analytic/Probability/ConditionalMeanApproximation](ConditionalMeanApproximation.md)
