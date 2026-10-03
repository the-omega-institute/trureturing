---
bibkey: abdesselam2022nonabelian
authors: Abdelmalek Abdesselam
year: 2022
title: "Non-Abelian correlation inequalities and stable determinantal polynomials"
doi: 10.48550/arXiv.2207.07603
url: https://arxiv.org/abs/2207.07603v2
claim: "Problem 3 asks whether Theorem 2.3, the PGG inequalities for stable determinantal polynomials, holds for every positive real exponent eta in place of positive half integers."
strata_touched:
  - D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation
license: citation-only
triage: anchor
---

# Non-Abelian correlation inequalities and stable determinantal polynomials

The following quotations are from arXiv:2207.07603v2, with the printed page numbers.

Page 4 defines row multiplication:

> Indeed, the multiindex $\alpha$ is here considered as a row vector of length $m$ while $V$ is a $m \times n$ matrix and $\alpha V$ simply denotes the matrix product.

Page 5 defines parity:

> Suppose we are given a group homomorphism ρ : ℤⁿ → (ℤ/2ℤ)ᴸ, for some integer L ≥ 0.

> We will say that a is even iff ρ(a) = 0.

Page 9 gives the matrix setting:

> Let q ∈ ℕ_{>0}, and let A₁, …, Aₙ be n real symmetric positive semidefinite matrices of q × q format. Suppose that A₁ + ⋯ + Aₙ is positive definite and define the polynomial P(x) = det(x₁A₁ + ⋯ xₙAₙ) which is then strictly positive for x ∈ (0, ∞)ⁿ.

> We also assume we have at our disposal a parity check homomorphism ρ : ℤⁿ → (ℤ/2ℤ)ᴸ and an associated definition of being even for multiindices $a\in\mathbb{N}^n$, as in the previous section.

Page 10 states Theorem 2.3:

> (The PGG inequalities for stable determinantal polynomials) For any $r\in\mathbb{N}_{>0}$, the substitute $a\mapsto\mathbb{1}\{a\ {\rm even}\}P(a)^{-\frac{r}{2}}$ for the map $a\mapsto\langle\mathcal{O}^a\rangle$ satisfies all the PGG inequalities. More precisely, $\forall m\ge 0$, $\forall V\in\mathbb{N}^{m\times n}$ such that $\mathbf{1}_m V$ is even, $\forall (\varepsilon_1,\ldots,\varepsilon_m)\in\{-1,1\}^m$, and for all even $u\in\mathbb{N}_{>0}^n$, we have
> $$\sum_{\substack{\alpha,\beta\in\mathbb{N}^m\\\alpha+\beta=\mathbf{1}_m}}\mathbb{1}\{\alpha V\ {\rm even}\}\varepsilon^{\beta}P(u+\alpha V)^{-\frac{r}{2}}P(u+\beta V)^{-\frac{r}{2}}\ge 0.$$

Page 14 asks:

> **Problem 3:** In the light of investigations of spin models with non-integer number of components N, as in [8], it would be interesting to see if Thm. 2.3 still holds for P^{−η} where η is any positive real number instead of being restricted to half integers.

The encoding uses zero-based `Fin` indices, real matrices, the additive homomorphism
`(Fin n → ℤ) →+ (Fin L → ZMod 2)`, and natural multi-indices cast to integers for
parity. A binary vector `α : Fin m → Fin 2` indexes each pair `α + β = 1` once,
with `β_i = 1 - α_i`. The sign is `ε^β = ∏ i, ε_i^{β_i}` (p. 6).
Row-vector multiplication uses Mathlib `Matrix.vecMul`.
All fractional powers are `Real.rpow`.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2207.07603
- URL: https://arxiv.org/abs/2207.07603v2
- PDF: https://arxiv.org/pdf/2207.07603v2, pp. 5, 9, 10 and 14.
