# A cutoff tradeoff for the weighted zeta sine sum

## Abstract

Effective linear independence gives a window bound for the actual weighted zeta sine sum.

**Definition 1.1 (The distinct positive ordinates).**

$$\forall h \in \mathrm{RH},\; \forall X \in \mathbb{R},\; \operatorname{G}\left(h, X\right) = \{\operatorname{Im}\left(\mathit{rho}\right) \mid \mathit{rho} \in Z \land \left(0 < \operatorname{Im}\left(\mathit{rho}\right) \land \operatorname{Im}\left(\mathit{rho}\right) \le X\right)\}$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedSineCutoff.positiveOrdinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here G(h,X) is a finite set of real numbers and Z is the set of nontrivial zeta zeros. The positive spectrum supplies the zeros through the inclusive cutoff X. RH puts them on the critical line, so taking imaginary parts is injective on that spectrum. `D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum`

Write N(X) for the canonical analytic multiplicity count in (0,X]. Each ordinate occurs once in G(h,X), and its zero contributes its analytic multiplicity to N(X).

**Definition 1.2 (Lamzouri's effective linear independence conjecture).**

$$\forall h \in \mathrm{RH},\; \operatorname{ELI}\left(h\right) \Leftrightarrow \left(\forall d \in \mathbb{R},\; 0 < d \Rightarrow \left(\exists C \in \mathbb{R},\; 0 < C \land \left(\forall X \in \mathbb{R},\; 2 \le X \Rightarrow \left(\forall k \in \mathbb{Z}^{\operatorname{G}\left(h, X\right)},\; \left(\left(\exists j \in \operatorname{G}\left(h, X\right),\; \operatorname{k}\left(j\right) \ne 0\right) \land \left(\forall j \in \operatorname{G}\left(h, X\right),\; \left|\operatorname{k}\left(j\right)\right| \le \operatorname{N}\left(X\right)\right)\right) \Rightarrow C \cdot \operatorname{exp}\left(-X^{1 + d}\right) \le \left|\sum_{j \in \operatorname{G}\left(h, X\right)} \operatorname{k}\left(j\right) \cdot j\right|\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedSineCutoff.EffectiveLI` (`✓ std3`).

*Citation.* Youness Lamzouri (2024). *An effective Linear Independence Conjecture for the zeros of the Riemann zeta function and applications*. DOI: [10.48550/arXiv.2311.04860](https://doi.org/10.48550/arXiv.2311.04860). URL: <https://arxiv.org/html/2311.04860v2>.

*Commentary.*

Conjecture 1.1 quantifies over every positive exponent slack d. The same positive C applies to every real X ≥ 2 and every nonzero integer coefficient family bounded by N(X). The source counts zeros in [0,X], which agrees with (0,X] for nontrivial zeta zeros under RH since there are no real ones. The conjecture allows C to be ineffective.

**Theorem 1.3 (A threshold attained in every window).**

$$\forall h \in \mathrm{RH},\; \operatorname{ELI}\left(h\right) \Rightarrow \left(\forall r \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall e \in \mathbb{R},\; \left(0 < r \land \left(0 < b \land 2 \cdot \left(1 - \operatorname{min}\left(b, 1\right)^{2}\right) < e\right)\right) \Rightarrow \operatorname{Eventually}\left((T \mapsto 0 < \operatorname{W}\left(h, T\right) \land \left(\forall a \in \mathbb{R},\; \exists u \in \mathbb{R},\; u \in [a, a + \operatorname{exp}\left(T^{b}\right)] \land 1 - \frac{\operatorname{S}\left(h, T, \frac{u}{r}\right)}{\operatorname{W}\left(h, T\right)} < e\right)), \mathit{atTop}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedSineCutoff.eventual_weighted_sine_cutoff_tradeoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Youness Lamzouri (2024). *An effective Linear Independence Conjecture for the zeros of the Riemann zeta function and applications*. DOI: [10.48550/arXiv.2311.04860](https://doi.org/10.48550/arXiv.2311.04860). URL: <https://arxiv.org/html/2311.04860v2>.

*Commentary.*

Write W(h,T) for harmonicMass and S(h,T,v) for weightedSine. Both use the same weight mγ γ/(1/4 + γ²) at each distinct positive ordinate, where mγ is analytic multiplicity. The variables b and e are the window exponent and the allowed normalized loss. The eventual quantifier at positive infinity gives one cutoff above which the bound holds for every T and every interval start a. `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine`

Choose 0 < α < min(b,1) and a positive prefix tolerance e₀ such that 2(1 − α²) + α² e₀ < e. Set X = T^α. Normalize the weights through X by W(h,X), use frequencies γ/r and target phase π/2, and fix an integer M with 1/M < e₀. Eventually M ≤ N(X). Effective linear independence then rules out nonzero resonant modes in the coefficient box and bounds their absolute scaled frequencies below by δ = C exp(−X^(1+d))/r. `D5/S3/Fourier/WeightedPhaseRecurrence`

Choose d > 0 with α(1+d) < b. The logarithm of the product of the window length and δ is T^b − T^(α(1+d)) + log(C/r). If D is the number of distinct prefix ordinates, D ≤ N(X) because each has multiplicity at least one, and N(X) = O(X log X). Therefore the logarithm of M^D is D log M = O(T^α log T). The positive T^b term eventually dominates both costs and the fixed constants. For R = exp(T^b) the recurrence inequality requires Rδ(e₀ − 1/M) > 2(e₀ M^D − (e₀ − 1/M)). It then gives prefix loss less than e₀ in every interval of length R.

The common limit of W(h,Y)/log²(Y) as Y tends to infinity is 1/(4π). In W(h,T^α)/W(h,T), the two normalized masses have ratio tending to one, while (log(T^α)/log T)² equals α² for T > 1. Thus the retained mass fraction q tends to α². On the omitted band, each sine can contribute loss at most twice its weight. The full normalized loss is less than 2(1 − q) + q e₀, which is eventually less than e by the strict parameter choice.

The result applies the finite recurrence theorem under RH and Conjecture 1.1 to the actual harmonic weights in every translated time interval of the stated length. Lamzouri's Theorem 1.5 concerns extreme values of Φ at truncation X² over [2,X] on the scale (log log log X)^A, for coefficient sequences satisfying Assumptions 1–3 and under ELI.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedSineCutoff.EffectiveLI`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedSineCutoff.eventual_weighted_sine_cutoff_tradeoff`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedSineCutoff.positiveOrdinates`
- Dependency: [D5/S3/Fourier/WeightedPhaseRecurrence](../../../../../Fourier/WeightedPhaseRecurrence.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine](RHRootWeightedSine.md)
- Narrative reference: [D5/S3/Fourier/WeightedPhaseRecurrence](../../../../../Fourier/WeightedPhaseRecurrence.md)
- Narrative reference: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine](RHRootWeightedSine.md)
- Narrative reference: [D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum](../../../../ZeroData/PositiveOrdinateSpectrum.md)
