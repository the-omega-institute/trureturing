# Speyer Uniform Normality

## Abstract

Growing uniform-matroid ranks satisfy both the central and local normal limit theorems.

**Definition 1.1 (g).**

$$\forall (n: \mathbb{N}), \forall (d: \mathbb{N}), \operatorname{g}\left(n, d\right) = \sum_{i \in \operatorname{Finset}.\operatorname{Icc}\left(1, \operatorname{min}\left(d, n - d\right)\right)} (\operatorname{C}\left(\frac{(\operatorname{Nat}.\operatorname{factorial}\left(n - i - 1\right): \mathbb{R})}{(\operatorname{Nat}.\operatorname{factorial}\left(d - i\right): \mathbb{R}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(n - d - i\right): \mathbb{R}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(i - 1\right): \mathbb{R})}\right) \cdot (X)^{i})$$

*Formalization.* `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.g` (`✓ std3`).

*Citation.* Rong Zhang, James Jing Yu Zhao (2024). *Analytic properties of Speyer’s g-polynomial of uniform matroids*. DOI: [10.1007/s10114-026-4502-5](https://doi.org/10.1007/s10114-026-4502-5). URL: <https://arxiv.org/abs/2408.15506v1>.

*Commentary.*

Proposition 1.1, page 1: “For any n ≥ 2 and 1 ≤ d ≤ n − 1, the g-polynomial of the uniform matroid Uₙ,ᵈ is given by” the displayed factorial sum. Every subtraction inside a factorial is natural-number subtraction; the factorial values are cast to the reals. The Lean index interval is Finset.Icc 1 (min d (n-d)).

**Theorem 1.2 (speyer_variance_eighth_unconditional).**

$$\forall (n: \mathbb{N}), \forall (d: \mathbb{N}), ((2 \le d) \land (2 \cdot d \le n)) \Rightarrow (\frac{((d - 1: \mathbb{N}): \mathbb{R})}{8} \le \operatorname{sigmaSq}\left(\operatorname{g}\left(n, d\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.speyer_variance_eighth_unconditional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The roots of the transported polynomial lie strictly below -1. Its logarithmic derivative at zero bounds the coefficient variance from below by (d-1)/8. Subtraction d-1 is performed in the natural numbers before casting. The bound holds when 2 ≤ d and 2*d ≤ n.

**Theorem 1.3 (speyer_variance_tendsto).**

$$\forall (d: \mathbb{N} \to \mathbb{N}), ((\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto (1 \le d\left(n\right)) \land (d\left(n\right) \le \operatorname{Nat}.\operatorname{div}\left(n, 2\right))), atTop\right)) \land (\operatorname{Tendsto}\left(d, atTop, atTop\right))) \Rightarrow (\operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \operatorname{sigmaSq}\left(\operatorname{g}\left(n, d\left(n\right)\right)\right)), atTop, atTop\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.speyer_variance_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For eventually admissible uniform-matroid ranks tending to infinity, the coefficient variances tend to infinity. Nat.div is natural-number division, so n/2 means the integer quotient.

**Theorem 1.4 (g_bernoulli_factorization).**

$$\forall (n: \mathbb{N}), \forall (d: \mathbb{N}), ((2 \le d) \land (2 \cdot d \le n)) \Rightarrow (\exists (m: \mathbb{N}), \exists (p: \operatorname{Fin}\left(m\right) \to \operatorname{unitInterval}), (\forall (i: \operatorname{Fin}\left(m\right)), (p\left(i\right): \mathbb{R}) \in \operatorname{Set}.\operatorname{Ioo}\left(0, 1\right)) \land (\operatorname{normalized}\left(\operatorname{g}\left(n, d\right)\right) = X \cdot \prod_{i: \operatorname{Fin}\left(m\right)} (\operatorname{bernoulliPGF}\left((p\left(i\right): \mathbb{R})\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.g_bernoulli_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* L. H. Harper (1967). *Stirling Behavior is Asymptotically Normal*. DOI: [10.1214/aoms/1177698956](https://doi.org/10.1214/aoms/1177698956). URL: <https://doi.org/10.1214/aoms/1177698956>.

*Commentary.*

The normalized Speyer polynomial is X times a product of Bernoulli probability-generating polynomials, with every parameter strictly between zero and one. Repeated differentiation in the Rodrigues identity gives the splitting of H. Reflection and reversal give the splitting of qAB, and positivity on [-1, infinity) puts its real roots below -1. Normalizing those factors gives the Bernoulli product; Harper is cited for the Bernoulli method.

**Definition 1.5 (claim).**

$$(claim) \Leftrightarrow (\forall (d: \mathbb{N} \to \mathbb{N}), (\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto (1 \le d\left(n\right)) \land (d\left(n\right) \le \operatorname{Nat}.\operatorname{div}\left(n, 2\right))), atTop\right)) \Rightarrow ((\operatorname{Tendsto}\left(d, atTop, atTop\right)) \Rightarrow ((\operatorname{CLT}\left((n: \mathbb{N} \mapsto \operatorname{g}\left(n, d\left(n\right)\right))\right)) \land (\operatorname{LLT}\left((n: \mathbb{N} \mapsto \operatorname{g}\left(n, d\left(n\right)\right))\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.claim` (`✓ std3`).

*Citation.* Rong Zhang, James Jing Yu Zhao (2024). *Analytic properties of Speyer’s g-polynomial of uniform matroids*. DOI: [10.1007/s10114-026-4502-5](https://doi.org/10.1007/s10114-026-4502-5). URL: <https://arxiv.org/abs/2408.15506v1>.

*Commentary.*

Conjecture 4.8, page 13, states verbatim: If d = d(n) is a real function of n such that d(n) → +∞ as n → +∞, then the coefficient of Speyer’s g-polynomial gₙ,ᵈ₍ₙ₎(t), namely Sᵢ(n,d(n)), is asymptotically normal by local and central limit theorems. The encoding uses an integer-valued rank sequence d, the eventual standing conditions 1 ≤ d(n) and d(n) ≤ Nat.div n 2, and Tendsto d atTop atTop. CLT and LLT are the uniform epsilon-form conventions above. The g-polynomial is the literal factorial sum of Proposition 1.1. The floor in LLT is an integer floor; Nat.div is natural-number division.

**Theorem 1.6 (result).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rong Zhang, James Jing Yu Zhao (2024). *Analytic properties of Speyer’s g-polynomial of uniform matroids*. DOI: [10.1007/s10114-026-4502-5](https://doi.org/10.1007/s10114-026-4502-5). URL: <https://arxiv.org/abs/2408.15506v1>.

*Commentary.*

Every eventually admissible rank sequence tending to infinity satisfies both limits. The normalized coefficient law is a shifted Bernoulli sum, and the lower bound (d-1)/8 forces its variance to diverge. The general Bernoulli limit theorem then gives CLT and LLT. Bounded rank lies outside this claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.claim`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.g`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.g_bernoulli_factorization`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.result`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.speyer_variance_eighth_unconditional`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.speyer_variance_tendsto`
