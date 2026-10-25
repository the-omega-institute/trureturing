# A modified Bessel ratio need not be log-concave

## Abstract

A positive rational series disproves log-concavity of a modified Bessel ratio.

**Definition 1.1 (The modified Bessel function of the first kind).**

$$\forall nu \in \mathbb {R},\; \forall z \in \mathbb {R},\; \operatorname {besselI}\left(nu, z\right) = \sum '_{k: \mathbb {N}} \frac{(\frac{z}{2})^{2 \cdot k + nu}}{\operatorname {Nat.factorial}\left(k\right) \cdot \operatorname {Real.Gamma}\left(k + nu + 1\right)}$$

*Formalization.* `D5/S3/Analytic/BesselRatioLogConcavity/Result.besselI` (`✓ std3`).

*Citation.* D. Karp, A. Vishnyakova, and Y. Zhang (2025). *Unimodality preservation by ratios of functional series and integral transforms*. DOI: [10.1007/s00025-025-02431-4](https://doi.org/10.1007/s00025-025-02431-4). URL: <https://arxiv.org/abs/2408.01755>.

*Commentary.*

Printed page 11 of arXiv:2408.01755v2 states: “with a > 0, b ≥ 0, ν > −1, µ > 0 and Iν standing for the modified Bessel function of the first kind.” It then states verbatim: “Using the standard power series expansion of Iν [28, p.217] we have”. The following displayed expansion of the ratio uses the series Iν(z)=∑ₖ₌₀∞(z/2)^(2k+ν)/(k! Γ(k+ν+1)). The definition is this real infinite sum, with the natural number 2k coerced to a real exponent. For z>0 and ν>−1 the series is summable: after the Gamma–Pochhammer identity its successive ratio tends to zero.

**Definition 1.2 (The positive-order log-concavity clause).**

$$claim = \left(\forall nu1 \in \mathbb {R},\; \forall nu2 \in \mathbb {R},\; \forall a1 \in \mathbb {R},\; \forall a2 \in \mathbb {R},\; 0 < nu2 \Rightarrow \left(nu2 \le nu1 \Rightarrow \left(0 < a1 \Rightarrow \left(a1 \le a2 \Rightarrow \operatorname {ConcaveOn}\left(\mathbb {R}, \operatorname {Set.Ioi}\left(0\right), x: \mathbb {R}\mapsto \operatorname {Real.log}\left(\frac{\operatorname {besselI}\left(nu1, a1 \cdot x\right)}{\operatorname {besselI}\left(nu2, a2 \cdot x\right)}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/BesselRatioLogConcavity/Result.claim` (`✓ std3`).

*Citation.* D. Karp, A. Vishnyakova, and Y. Zhang (2025). *Unimodality preservation by ratios of functional series and integral transforms*. DOI: [10.1007/s00025-025-02431-4](https://doi.org/10.1007/s00025-025-02431-4). URL: <https://arxiv.org/abs/2408.01755>.

*Commentary.*

Conjecture 1, printed page 12, with line breaks joined: “Conjecture 1. Suppose b ≥ 0, ν1 ≥ ν2 > −1 and 0 < a1 ≤ a2. Then the ratio x → Iν1(a1 x)/Iν2(a2 x) is unimodal on (0, ∞). Moreover, if ν1 ≥ ν2 > 0 it is log-concave.”

The claim quantifies over all real orders nu1≥nu2>0 and all scales 0<a1≤a2. It states concavity on the entire positive real half-line of the logarithm of the standard modified Bessel ratio. Positivity of the series on this domain makes that the usual log-concavity assertion. The parameter b in the source does not occur in the ratio. Its unimodality clause is a separate assertion.

**Theorem 1.3 (An exact infinite-series counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/karp-vishnyakova-zhang-2025-bessel-ratio-log-concavity` (refuted) by `D5/S3/Analytic/BesselRatioLogConcavity/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"karp-vishnyakova-zhang-2025-bessel-ratio-log-concavity","declaration_gid":"D5/S3/Analytic/BesselRatioLogConcavity/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. Karp, A. Vishnyakova, and Y. Zhang (2025). *Unimodality preservation by ratios of functional series and integral transforms*. DOI: [10.1007/s00025-025-02431-4](https://doi.org/10.1007/s00025-025-02431-4). URL: <https://arxiv.org/abs/2408.01755>.

*Commentary.*

Take equal orders nu1=nu2=1/10 and scales a1=1,a2=2. Write S(w)=∑ₖ₌₀∞ w^k/(k! (11/10)ₖ). The Gamma–Pochhammer identity gamma_pochhammer gives Iν(t)/Iν(2t)=2^(−ν) S(t²/4)/S(t²). Gamma factors cancel, and the positive real power factor is common to all three points.

For a nonnegative rational w, let L(w) be the sum over 0≤k<60, let t60(w) be the term of index 60, and put rho(w)=w/(61·(611/10)). Every successive ratio starting at index 60 is at most rho(w). When rho(w)<1, the infinite series lies between L(w) and L(w)+t60(w)/(1−rho(w)). Exact rational arithmetic gives S(9/16)≥1.584, S(225/16)≥223.368 and S(81/4)≥894.574, while S(81/16)≤15.316, S(9/4)≤4.447 and S(225/4)≤264068.

These bounds imply S(9/16)S(225/16)S(81/4)²>S(81/16)²S(9/4)S(225/4). Thus R(3/2)R(15/2)>R(9/2)² for R(t)=I₁⁄₁₀(t)/I₁⁄₁₀(2t). Taking logarithms contradicts concavity at the midpoint 9/2. This disproves the universal log-concavity clause; it leaves unimodality and the full parameter range of log-concavity unresolved.

## References

- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.besselI`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.claim`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.result`
- Dependency: [D5/S3/Analytic/KummerRatio/BetaIntegral](../KummerRatio/BetaIntegral.md)
