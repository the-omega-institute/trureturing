# Golden Germ Normalized Factor Regularity

## Abstract

Cancellation makes the normalized golden germ product holomorphic above one over phi cubed and continuous at one over phi squared.

**Theorem 1.1 (The normalized golden germ factor is regular at the zeta boundary).**

$$\begin{aligned}G: \mathbb{C} \to \mathbb{C},\\\forall s\in \mathbb{C}, \operatorname{G}(s) := \prod_{p\in \operatorname{Primes}(\mathbb{N})}(1 - p^{-s \times \varphi^{2}}) \times \sum_{v\in \mathbb{N}}p^{-s \times \operatorname{o5Beta}(v)},\\(\forall sigma\in \mathbb{R}, \frac{1}{\varphi^{3}} < sigma \Rightarrow \exists u: \operatorname{Primes}(\mathbb{N}) \to \mathbb{R}, \operatorname{Summable}(u) \land \forall p\in \operatorname{Primes}(\mathbb{N}), \forall s\in \mathbb{C}, sigma < \Re(s) \Rightarrow \left\lVert (1 - p^{-s \times \varphi^{2}}) \times \sum_{v\in \mathbb{N}}p^{-s \times \operatorname{o5Beta}(v)} - 1 \right\rVert \leq \operatorname{u}(p)) \land\\\operatorname{ContinuousOn}(G, \{s\in \mathbb{C} \mid \frac{1}{\varphi^{3}} < \Re(s)\}) \land\\\operatorname{ContinuousAt}(G, \frac{1}{\varphi^{2}}) \land\\\operatorname{AnalyticOnNhd}(\mathbb{C}, G, \{s\in \mathbb{C} \mid \frac{1}{\varphi^{3}} < \Re(s)\}).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Regularity/GoldenGermNormalizedFactorRegularity.golden_germ_normalized_factor_regularity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each real sigma strictly above one over phi cubed, the proof constructs a prime-indexed summable majorant. It bounds the normalized local-factor deviation simultaneously for every complex s with real part greater than sigma.

The local golden series is split into its vacuum term, its first excited mode p^(-s phi^2), and the tail beginning at beta two. Multiplication by one minus the first mode cancels the linear term. The remaining tail, squared first mode, and their product are dominated by summable families at sigma.

Each fixed-prime local series is holomorphic on the same half-plane. Pinned Mathlib's locally uniform infinite-product theorem applies to the uniform majorant, and finite products are holomorphic. The locally uniform limit is therefore holomorphic on the full region where the real part exceeds one over phi cubed.

Since one over phi squared is strictly greater than one over phi cubed, it is an interior point of this holomorphy region. The displayed ContinuousAt conclusion follows from the regional continuity, rather than from pointwise summability alone.

STOPPING JUSTIFICATION: this theorem supplies the regularity input isolated by GoldenGermZetaBoundary, but it does not itself state the downstream singularity conclusion for the continued germ. That conclusion requires a distinct theorem combining this continuity with the frozen boundary identity, transported zeta residue, and nonvanishing. No convergence or regularity at or to the left of one over phi cubed is asserted.

## References

- Truth anchor: `D5/S3/Analytic/Regularity/GoldenGermNormalizedFactorRegularity.golden_germ_normalized_factor_regularity`
