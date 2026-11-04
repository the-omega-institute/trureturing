---
bibkey: coskuneden2025vidinli
authors: "O. Coşkun and A. Eden"
year: 2025
title: "Structure of Vidinli Algebras: Simple Nonassociative Jordan–Lie Algebras with Azumaya Properties"
doi: 10.48550/arXiv.2511.09395
url: https://arxiv.org/abs/2511.09395v1
claim: "Definition 5.1 gives the exceptional Vidinli product; Remark 5.9 asks whether it is a linear push-forward of octonion multiplication."
strata_touched:
  - D5/S3/HomologicalAlgebra/CoskunEdenVidinliOctonion
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2511.09395

Source: https://arxiv.org/abs/2511.09395v1

## Product and question

Definition 5.1 and its coordinate expression, pp. 19–20:

> a ⊻₇ b = c₁e₁ + ∑_{i=2}^{7} cᵢeᵢ, where c₁ = a₁b₁ − ∑_{i=2}^{7} aᵢbᵢ + (a₂b₃ − a₃b₂) + (a₄b₅ − a₅b₄) + (a₆b₇ − a₇b₆), cᵢ = a₁bᵢ + b₁aᵢ for i = 2, …, 7.

Remark 5.9, p. 23:

> By [5, Proposition 9], see also Section 3.1, the Vidinli multiplication in dimension three arises as a push-forward of quaternion multiplication. Whether a similar push-forward description exists for the exceptional Vidinli algebra V₇ in terms of the octonions, or more generally for V_{2^k−1} in relation to higher Cayley-Dickson algebras, remains an open question.

The Lean product uses `Fin 7 → ℝ`, with index `i` representing the source's
coordinate `i + 1`. The octonion clause asks for real-linear maps
`ν : V₇ → 𝕆` and `π : 𝕆 → V₇` such that
`vidinliMul a b = π (mul (ν a) (ν b))` for every `a` and `b`.
The octonion multiplication is the signed Cayley–Dickson coordinate model
`D5.S3.VertexAlgebra.MonsterTwistedOctonionNorm.mul`.

The repository result refutes this octonion clause using norm multiplicativity
and rank-nullity. The higher Cayley–Dickson clause is outside its scope.
The question is from v1; v2 has a different title and omits the question.
Literature-search completeness is `ASSUMED-UNVERIFIED`; see
[the source and literature screen](https://github.com/the-omega-institute/trureturing/issues/20661).
