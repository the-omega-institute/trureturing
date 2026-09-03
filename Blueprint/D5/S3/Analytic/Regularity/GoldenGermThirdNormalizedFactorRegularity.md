# Golden Germ Third Normalized Factor Regularity

## Abstract

The third normalized golden germ product is holomorphic above one over phi to the fifth, is zero-free on the established complex half-plane, and is continuous and nonzero at one over phi to the fourth.

**Theorem 1.1 (The third normalized factor is regular beyond the phi-fifth threshold).**

$$\begin{aligned}\forall s\in \mathbb{C}, p\in \operatorname{Primes}(\mathbb{N}),\\\operatorname{x}(s, p) := p^{-s \times \varphi^{2}}, \operatorname{y}(s, p) := p^{-s \times \varphi^{3}}, \operatorname{Kp}(s, p) := (1 - \operatorname{y}(s, p)^{2})^{-1} \times (1 - \operatorname{x}(s, p)^{2} \times \operatorname{y}(s, p)) \times (1 - \operatorname{y}(s, p)) \times (1 + \operatorname{x}(s, p))^{-1} \times \sum_{v\in \mathbb{N}}p^{-s \times \operatorname{o5Beta}(v)},\\\forall s\in \mathbb{C}, \operatorname{G3}(s) := \prod_{p\in \operatorname{Primes}(\mathbb{N})}\operatorname{Kp}(s, p),\\(\forall sigma\in \mathbb{R}, \frac{1}{\varphi^{5}} < sigma \Rightarrow \exists u: \operatorname{Primes}(\mathbb{N}) \to \mathbb{R}, \operatorname{Summable}(u) \land \forall p\in \operatorname{Primes}(\mathbb{N}), \forall s\in \mathbb{C}, sigma \leq \Re(s) \Rightarrow \left\lVert \operatorname{Kp}(s, p) - 1 \right\rVert \leq \operatorname{u}(p)) \land\\\operatorname{AnalyticOnNhd}(\mathbb{C}, G3, \{s\in \mathbb{C} \mid \frac{1}{\varphi^{5}} < \Re(s)\}) \land\\(\forall s\in \mathbb{C}, \frac{3}{5} \leq \Re(s) \Rightarrow \operatorname{G3}(s) \neq 0) \land\\(\forall sigma\in \mathbb{R}, \frac{1}{\varphi^{5}} < sigma \Rightarrow \operatorname{G3}(sigma) \neq 0) \land\\\operatorname{ContinuousAt}(G3, \frac{1}{\varphi^{4}}) \land\\\operatorname{G3}(\frac{1}{\varphi^{4}}) \neq 0.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorRegularity.golden_germ_third_normalized_factor_regularity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem is the regularity step after the third-order ledger and factorization in the golden Euler germ extraction ladder of OACTC Parts 580 and 581. It advances the previously open analytic boundary by upgrading frozen pointwise deviation summability to a locally uniform product.

For every real sigma strictly above one over phi to the fifth, the proof splits the local series after six modes. Boundary-line norms for the retained mixed modes and tail form a prime-summable majorant valid simultaneously whenever the real part is at least sigma. The same estimates keep one plus x and one minus y-squared away from zero.

Each fixed-prime factor is holomorphic: its complex powers are entire in s, the two denominators are nonzero, and the germ-local series uses the frozen positive-half-plane analyticity theorem. Pinned Mathlib's locally uniform infinite-product theorem then makes the prime product holomorphic throughout the open target half-plane.

Complex nonvanishing is asserted only when the real part is at least three fifths, where the frozen germ product theorem forces every local germ factor to be nonzero. On the wider target region, every positive real point is nonzero because each real local series is a convergent sum of nonnegative terms with vacuum term one. This includes one over phi to the fourth, whose continuity follows from being an interior point of the holomorphy region.

The theorem does not assert complex nonvanishing on all of the half-plane above one over phi to the fifth, regularity on its boundary, a fourth or all-order extraction, O-5, or the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorRegularity.golden_germ_third_normalized_factor_regularity`
- Dependency: [D5/S3/Analytic/EulerGerm/GermProductNonvanishingAboveThreeFifths](../EulerGerm/GermProductNonvanishingAboveThreeFifths.md)
- Dependency: [D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderFactorization](../EulerGerm/GoldenGermThirdOrderFactorization.md)
- Dependency: [D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderLedger](../EulerGerm/GoldenGermThirdOrderLedger.md)
- Dependency: [D5/S3/Analytic/EulerGerm/LocalFactorZeroDivisor](../EulerGerm/LocalFactorZeroDivisor.md)
- Dependency: [D5/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorMajorant](GoldenGermThirdNormalizedFactorMajorant.md)
