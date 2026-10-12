# Speyer Uniform Normality

## Abstract

Growing uniform-matroid ranks satisfy both the central and local normal limit theorems.

**Definition 1.1 (claim).**

$$(claim) \Leftrightarrow (\forall (d: \mathbb{N} \to \mathbb{N}), (\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto (1 \le d\left(n\right)) \land (d\left(n\right) \le \operatorname{Nat}.\operatorname{div}\left(n, 2\right))), atTop\right)) \Rightarrow ((\operatorname{Tendsto}\left(d, atTop, atTop\right)) \Rightarrow ((\operatorname{CLT}\left((n: \mathbb{N} \mapsto \operatorname{g}\left(n, d\left(n\right)\right))\right)) \land (\operatorname{LLT}\left((n: \mathbb{N} \mapsto \operatorname{g}\left(n, d\left(n\right)\right))\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.claim` (`✓ std3`).

*Citation.* Rong Zhang, James Jing Yu Zhao (2024). *Analytic properties of Speyer’s g-polynomial of uniform matroids*. DOI: [10.1007/s10114-026-4502-5](https://doi.org/10.1007/s10114-026-4502-5). URL: <https://arxiv.org/abs/2408.15506v1>.

*Commentary.*

Conjecture 4.8, page 13, states verbatim: If d = d(n) is a real function of n such that d(n) → +∞ as n → +∞, then the coefficient of Speyer’s g-polynomial gₙ,ᵈ₍ₙ₎(t), namely Sᵢ(n,d(n)), is asymptotically normal by local and central limit theorems. The encoding uses an integer-valued rank sequence d, the eventual standing conditions 1 ≤ d(n) and d(n) ≤ Nat.div n 2, and Tendsto d atTop atTop. CLT and LLT are the uniform epsilon-form conventions above. The g-polynomial is the literal factorial sum of Proposition 1.1. The floor in LLT is an integer floor; Nat.div is natural-number division.

**Theorem 1.2 (result).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-zhao-2024-speyer-g-uniform-normality` (proved) by `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-zhao-2024-speyer-g-uniform-normality","declaration_gid":"D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Rong Zhang, James Jing Yu Zhao (2024). *Analytic properties of Speyer’s g-polynomial of uniform matroids*. DOI: [10.1007/s10114-026-4502-5](https://doi.org/10.1007/s10114-026-4502-5). URL: <https://arxiv.org/abs/2408.15506v1>.

*Commentary.*

Every eventually admissible rank sequence tending to infinity satisfies both limits. The normalized coefficient law is a shifted Bernoulli sum, and the lower bound (d-1)/8 forces its variance to diverge. The general Bernoulli limit theorem then gives CLT and LLT. Bounded rank lies outside this claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.claim`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.result`
- Dependency: [D5/S3/Combinatorics/Matroids/SpeyerUniformVariance](SpeyerUniformVariance.md)
