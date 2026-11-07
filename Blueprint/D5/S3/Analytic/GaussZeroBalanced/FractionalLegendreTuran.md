# Fractional-degree Legendre Turán inequality

## Abstract

A rational interior counterexample to Karp's fractional Legendre Turán inequality.

**Definition 1.1 (Conjecture 4).**

$$claim = (\forall (\mu: \mathbb{R}), \forall (\delta: \mathbb{R}), \forall (y: \mathbb{R}), 0 < \mu \Rightarrow \left(0 < \delta \Rightarrow \left(\delta < 1 \Rightarrow \left(0 < y \Rightarrow \left(y < 1 \Rightarrow \operatorname{gauss}\left(-\mu, 1 + \mu, 1, y\right)^{2} > \operatorname{gauss}\left(-\mu - \delta, 1 + \mu + \delta, 1, y\right) \cdot \operatorname{gauss}\left(-\mu + \delta, 1 + \mu - \delta, 1, y\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Analytic/GaussZeroBalanced/FractionalLegendreTuran.claim` (`✓ std3`).

*Citation.* Dmitry Karp (2011). *Log-convexity and log-concavity for series in product ratios of rising factorials and gamma functions*. URL: <https://math.nist.gov/~DLozier/SF21/SF21slides/Karp.pdf>.

*Commentary.*

Karp, SF21 slides, physical PDF p. 52 (also pp. 53–54), verbatim: “Curious open problems”; “Turán (1946) inequality for Legendre polynomials:”

“₂F₁(−μ,1+μ;1;y)² > ₂F₁(−μ−δ,1+μ+δ;1;y)₂F₁(−μ+δ,1+μ−δ;1;y),”

“for y∈(0,1), μ=1,2,… and δ=1.” “Conjecture 4” “Turán inequality is true for all μ>0 and 0<δ<1.”

The real function gauss is the existing ordinaryHypergeometric over ℝ. The letters μ, δ and y are real numbers; the argument retains the open interval from the preceding display. The first product factor has degree μ+δ and the second degree μ−δ. No sign or zero-free restriction on the three values is imposed.

**Theorem 1.2 (The fractional-degree assertion is false).**

$$\neg (\forall (\mu: \mathbb{R}), \forall (\delta: \mathbb{R}), \forall (y: \mathbb{R}), 0 < \mu \Rightarrow \left(0 < \delta \Rightarrow \left(\delta < 1 \Rightarrow \left(0 < y \Rightarrow \left(y < 1 \Rightarrow \operatorname{gauss}\left(-\mu, 1 + \mu, 1, y\right)^{2} > \operatorname{gauss}\left(-\mu - \delta, 1 + \mu + \delta, 1, y\right) \cdot \operatorname{gauss}\left(-\mu + \delta, 1 + \mu - \delta, 1, y\right)\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/FractionalLegendreTuran.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitry Karp (2011). *Log-convexity and log-concavity for series in product ratios of rising factorials and gamma functions*. URL: <https://math.nist.gov/~DLozier/SF21/SF21slides/Karp.pdf>.

*Commentary.*

Take μ=3/2, δ=63/64 and y=4095/4096. The values at degrees 33/64, 96/64 and 159/64 lie respectively in [−23/10,−227/100], [181/100,184/100] and [−153/100,−150/100]. The central square is at most (184/100)², whereas the shifted product is at least (227/100)(150/100); their difference is strictly negative.

The integer certificates enclose 10,000 recurrence steps at scale 10¹². Beyond a degree-dependent index the absolute term ratio is at most y, so the remaining series is bounded geometrically. All three degrees are positive. This strict interior counterexample also contradicts the non-strict comparison. Variants requiring positive function values or a zero-free range, and a uniform moving-shift family, remain open.

## References

- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/FractionalLegendreTuran.claim`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/FractionalLegendreTuran.result`
- Dependency: [D5/S3/Analytic/GaussZeroBalanced/Defs](Defs.md)
- Dependency: [D5/S3/Analytic/GaussZeroBalanced/Series](Series.md)
