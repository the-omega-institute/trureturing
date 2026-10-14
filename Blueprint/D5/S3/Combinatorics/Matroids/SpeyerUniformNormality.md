# Speyer Uniform Normality

## Abstract

Growing uniform-matroid ranks satisfy both the central and local normal limit theorems.

**Definition 1.1 (g).**

$$\forall (n: \mathbb{N}), \forall (d: \mathbb{N}), \operatorname{g}\left(n, d\right) = \sum_{i \in \operatorname{Finset}.\operatorname{Icc}\left(1, \operatorname{min}\left(d, n - d\right)\right)} (\operatorname{C}\left(\frac{(\operatorname{Nat}.\operatorname{factorial}\left(n - i - 1\right): \mathbb{R})}{(\operatorname{Nat}.\operatorname{factorial}\left(d - i\right): \mathbb{R}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(n - d - i\right): \mathbb{R}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(i - 1\right): \mathbb{R})}\right) \cdot (X)^{i})$$

*Formalization.* `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.g` (`✓ std3`).

*Citation.* Rong Zhang, James Jing Yu Zhao (2024). *Analytic properties of Speyer’s g-polynomial of uniform matroids*. DOI: [10.1007/s10114-026-4502-5](https://doi.org/10.1007/s10114-026-4502-5). URL: <https://arxiv.org/abs/2408.15506v1>.

*Commentary.*

Proposition 1.1, page 1: “For any n ≥ 2 and 1 ≤ d ≤ n − 1, the g-polynomial of the uniform matroid Uₙ,ᵈ is given by” the displayed factorial sum. Every subtraction inside a factorial is natural-number subtraction; the factorial values are cast to the reals. The Lean index interval is Finset.Icc 1 (min d (n-d)).

**Definition 1.2 (claim).**

$$(claim) \Leftrightarrow (\forall (d: \mathbb{N} \to \mathbb{N}), (\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto (1 \le d\left(n\right)) \land (d\left(n\right) \le \operatorname{Nat}.\operatorname{div}\left(n, 2\right))), atTop\right)) \Rightarrow ((\operatorname{Tendsto}\left(d, atTop, atTop\right)) \Rightarrow ((\forall (e: \mathbb{R}), (0 < e) \Rightarrow (\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto \forall (t: \mathbb{R}), \left|\sum_{k \in \operatorname{filter}\left((k: \mathbb{N} \mapsto (k: \mathbb{R}) \le \operatorname{mu}\left(\operatorname{g}\left(n, d\left(n\right)\right)\right) + t \cdot \operatorname{sigma}\left(\operatorname{g}\left(n, d\left(n\right)\right)\right)), \operatorname{range}\left(\operatorname{natDegree}\left(\operatorname{g}\left(n, d\left(n\right)\right)\right) + 1\right)\right)} (\operatorname{prob}\left(\operatorname{g}\left(n, d\left(n\right)\right), (k: \mathbb{Z})\right)) - (\operatorname{Real}.\operatorname{sqrt}\left(2 \cdot \pi\right))^{-1} \cdot \int x \in \operatorname{Set}.\operatorname{Iic}\left(t\right), \operatorname{exp}\left(-\frac{(x)^{2}}{2}\right)\right| < e), atTop\right))) \land (\forall (e: \mathbb{R}), (0 < e) \Rightarrow (\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto \forall (t: \mathbb{R}), \left|\operatorname{sigma}\left(\operatorname{g}\left(n, d\left(n\right)\right)\right) \cdot \operatorname{prob}\left(\operatorname{g}\left(n, d\left(n\right)\right), \left\lfloor \operatorname{mu}\left(\operatorname{g}\left(n, d\left(n\right)\right)\right) + t \cdot \operatorname{sigma}\left(\operatorname{g}\left(n, d\left(n\right)\right)\right)\right\rfloor\right) - (\operatorname{Real}.\operatorname{sqrt}\left(2 \cdot \pi\right))^{-1} \cdot \operatorname{exp}\left(-\frac{(t)^{2}}{2}\right)\right| < e), atTop\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.claim` (`✓ std3`).

*Citation.* Rong Zhang, James Jing Yu Zhao (2024). *Analytic properties of Speyer’s g-polynomial of uniform matroids*. DOI: [10.1007/s10114-026-4502-5](https://doi.org/10.1007/s10114-026-4502-5). URL: <https://arxiv.org/abs/2408.15506v1>.

*Commentary.*

Conjecture 4.8, page 13, states verbatim: If d = d(n) is a real function of n such that d(n) → +∞ as n → +∞, then the coefficient of Speyer’s g-polynomial gₙ,ᵈ₍ₙ₎(t), namely Sᵢ(n,d(n)), is asymptotically normal by local and central limit theorems. The encoding uses an integer-valued rank sequence d, the eventual standing conditions 1 ≤ d(n) and d(n) ≤ Nat.div n 2, and Tendsto d atTop atTop. Both displayed limits use the source Gaussian integral and density. The proof uses StatLean.HypothesisTesting.stdNormalCDF and stdNormalPDF through their corresponding formulas. The g-polynomial is the literal factorial sum of Proposition 1.1. The floor in the local limit is an integer floor; Nat.div is natural-number division.

**Theorem 1.3 (result).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rong Zhang, James Jing Yu Zhao (2024). *Analytic properties of Speyer’s g-polynomial of uniform matroids*. DOI: [10.1007/s10114-026-4502-5](https://doi.org/10.1007/s10114-026-4502-5). URL: <https://arxiv.org/abs/2408.15506v1>.

*Commentary.*

Every eventually admissible rank sequence tending to infinity satisfies both limits. The normalized coefficient law is a shifted Bernoulli sum, and the lower bound (d-1)/8 forces its variance to diverge. The general Bernoulli limit theorem then gives CLT and LLT. Bounded rank lies outside this claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.claim`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.g`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.result`
- Dependency: [D5/S3/Analytic/Probability/BernoulliTriangularLimits](../../Analytic/Probability/BernoulliTriangularLimits.md)
