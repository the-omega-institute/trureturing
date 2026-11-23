# Power cutoffs for weighted sine recurrence

## Abstract

Finite character separation and a retained mass bound give uniform weighted sine recurrence.

Fix a locally finite positive spectrum with index type I, frequency γ(j) and nonnegative weights w(j). Write J(T) for the finite set of indices satisfying γ(j) ≤ T. `D5/S3/Analytic/Oscillation/OrdinateCounting`

**Definition 1.1 (Spectral mass).**

$$\forall T \in \mathbb{R},\; \operatorname{W}\left(T\right) = \sum_{j \in \operatorname{J}\left(T\right)} \operatorname{w}\left(j\right)$$

*Formalization.* `D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cutoff is inclusive.

**Definition 1.2 (Weighted sine score).**

$$\forall T \in \mathbb{R},\; \forall v \in \mathbb{R},\; \operatorname{S}\left(T, v\right) = \sum_{j \in \operatorname{J}\left(T\right)} \operatorname{w}\left(j\right) \cdot \operatorname{sin}\left(\operatorname{gamma}\left(j\right) \cdot v\right)$$

*Formalization.* `D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff.sine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The score uses the same weights as W.

**Definition 1.3 (Separation on each fixed coefficient box).**

$$G \Leftrightarrow \left(\forall d \in \mathbb{R},\; 0 < d \Rightarrow \left(\exists C \in \mathbb{R},\; 0 < C \land \left(\forall M \in \mathbb{N},\; \operatorname{Eventually}\left((X \mapsto \forall k \in \mathbb{Z}^{\operatorname{J}\left(X\right)},\; \left(\left(\exists j \in \operatorname{J}\left(X\right),\; \operatorname{k}\left(j\right) \ne 0\right) \land \left(\forall j \in \operatorname{J}\left(X\right),\; \left|\operatorname{k}\left(j\right)\right| \le M\right)\right) \Rightarrow C \cdot \operatorname{exp}\left(-X^{1 + d}\right) \le \left|\sum_{j \in \operatorname{J}\left(X\right)} \operatorname{k}\left(j\right) \cdot \operatorname{gamma}\left(j\right)\right|), \mathit{atTop}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff.HasBoxGap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Youness Lamzouri (2024). *An effective Linear Independence Conjecture for the zeros of the Riemann zeta function and applications*. DOI: [10.48550/arXiv.2311.04860](https://doi.org/10.48550/arXiv.2311.04860). URL: <https://arxiv.org/html/2311.04860v2>.

*Commentary.*

One positive C works for every fixed integer bound M at the chosen exponent slack d. The cutoff from which the inequality holds may depend on M.

**Theorem 1.4 (A weighted sine threshold in every translated window).**

$$\left(\left(\forall j \in I,\; 0 \le \operatorname{w}\left(j\right)\right) \land \left(\operatorname{Eventually}\left((T \mapsto 0 < \operatorname{W}\left(T\right)), \mathit{atTop}\right) \land \left(\left(\exists B \in \mathbb{R},\; 0 < B \land \operatorname{Eventually}\left((X \mapsto \operatorname{D}\left(X\right) \le B \cdot X \cdot \operatorname{log}\left(X\right)), \mathit{atTop}\right)\right) \land \left(G \land \left(\forall alpha \in \mathbb{R},\; \left(0 < \mathit{alpha} \land \mathit{alpha} < 1\right) \Rightarrow \left(\exists q \in \mathbb{R},\; \mathit{alpha}^{2} \le q \land \operatorname{Tendsto}\left((T \mapsto \frac{\operatorname{W}\left(T^{\mathit{alpha}}\right)}{\operatorname{W}\left(T\right)}), \mathit{atTop}, \operatorname{nhds}\left(q\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall r \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall e \in \mathbb{R},\; \left(0 < r \land \left(0 < b \land 2 \cdot \left(1 - \operatorname{min}\left(b, 1\right)^{2}\right) < e\right)\right) \Rightarrow \operatorname{Eventually}\left((T \mapsto 0 < \operatorname{W}\left(T\right) \land \left(\forall a \in \mathbb{R},\; \exists u \in \mathbb{R},\; u \in [a, a + \operatorname{exp}\left(T^{b}\right)] \land 1 - \frac{\operatorname{S}\left(T, \frac{u}{r}\right)}{\operatorname{W}\left(T\right)} < e\right)), \mathit{atTop}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff.eventual_sine_cutoff_tradeoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Youness Lamzouri (2024). *An effective Linear Independence Conjecture for the zeros of the Riemann zeta function and applications*. DOI: [10.48550/arXiv.2311.04860](https://doi.org/10.48550/arXiv.2311.04860). URL: <https://arxiv.org/html/2311.04860v2>.

*Commentary.*

Write D(X) = |J(X)| and G for the coefficient box separation condition. W and S use the same arbitrary weight family. For every 0 < α < 1, the assumed retained mass fraction W(T^α)/W(T) converges to a value q at least α².

Choose 0 < α < min(b,1) and 0 < e₀ ≤ 1 with 2(1 − α²) + α²e₀ < e. Set X = T^α and choose a positive integer M with 1/M < e₀. Apply the finite recurrence at frequencies γ(j)/r and target angle π/2, with probabilities w(j)/W(X). The gap condition gives δ = C exp(−X^(1+d))/r. `D5/S3/Fourier/WeightedPhaseRecurrence`

Pick d > 0 with α(1+d) < b. The logarithm of exp(T^b)δ is T^b − T^(α(1+d)) + log(C/r). The bound on D(X) gives D(X) log M = O(T^α log T). The two growth costs and the fixed constants fit the strict recurrence budget. The retained score therefore has normalized loss below e₀ at a point in every window.

At that point the omitted coordinates contribute at most twice their weight to the full loss. With q_T = W(X)/W(T), the full normalized loss is less than 2(1 − q_T) + q_T e₀. This expression decreases with q_T, and its limit is below e.

For the actual positive zeta ordinates, assume RH and Lamzouri's Conjecture 1.1. Use mγ γ/(1/4 + γ²) as the weight, where mγ is the analytic multiplicity. The count N(X) eventually exceeds any fixed M, so the conjecture supplies G. Distinct mode count is bounded by N(X), which is O(X log X), and W(T)/log² T tends to 1/(4π). Hence W(T)>0 eventually and q = α². The specialization gives the displayed bound for these actual weights under the two conjectures. `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine`

Lamzouri's Theorem 1.5 concerns the extrema on [2,X] of sums truncated at X² under Effective LI and its coefficient assumptions.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff.HasBoxGap`
- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff.eventual_sine_cutoff_tradeoff`
- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff.mass`
- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff.sine`
- Dependency: [D5/S3/Analytic/Oscillation/OrdinateCounting](OrdinateCounting.md)
- Dependency: [D5/S3/Fourier/WeightedPhaseRecurrence](../../Fourier/WeightedPhaseRecurrence.md)
- Narrative reference: [D5/S3/Analytic/Oscillation/OrdinateCounting](OrdinateCounting.md)
- Narrative reference: [D5/S3/Fourier/WeightedPhaseRecurrence](../../Fourier/WeightedPhaseRecurrence.md)
- Narrative reference: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine](../../Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine.md)
