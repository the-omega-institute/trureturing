# No octonion push-forward for the exceptional Vidinli algebra

## Abstract

The exceptional seven-dimensional Vidinli product is not a linear push-forward of octonion multiplication.

**Definition 1.1 (The exceptional Vidinli product).**

$$\forall a: \operatorname{Fin}\left(7\right) \to \mathbb{R}, \forall b: \operatorname{Fin}\left(7\right) \to \mathbb{R}, \operatorname{vidinliMul}\left(a, b\right) = (\lambda i: \operatorname{Fin}\left(7\right) \mapsto \operatorname{ite}\left(i = 0, a\left(0\right) \cdot b\left(0\right) - \sum_{j \in \operatorname{Finset.Ioi}\left((0: \operatorname{Fin}\left(7\right))\right)} (a\left(j\right) \cdot b\left(j\right)) + (a\left(1\right) \cdot b\left(2\right) - a\left(2\right) \cdot b\left(1\right)) + (a\left(3\right) \cdot b\left(4\right) - a\left(4\right) \cdot b\left(3\right)) + (a\left(5\right) \cdot b\left(6\right) - a\left(6\right) \cdot b\left(5\right)), a\left(0\right) \cdot b\left(i\right) + b\left(0\right) \cdot a\left(i\right)\right))$$

*Formalization.* `D5/S3/HomologicalAlgebra/CoskunEdenVidinliOctonion.vidinliMul` (`✓ std3`).

*Citation.* O. Coşkun and A. Eden (2025). *Structure of Vidinli Algebras: Simple Nonassociative Jordan–Lie Algebras with Azumaya Properties*. DOI: [10.48550/arXiv.2511.09395](https://doi.org/10.48550/arXiv.2511.09395). URL: <https://arxiv.org/abs/2511.09395v1>.

*Commentary.*

Definition 5.1 and its coordinate expression, pp. 19–20: “a ⊻₇ b = c₁e₁ + ∑_{i=2}^{7} cᵢeᵢ, where c₁ = a₁b₁ − ∑_{i=2}^{7} aᵢbᵢ + (a₂b₃ − a₃b₂) + (a₄b₅ − a₅b₄) + (a₆b₇ − a₇b₆), cᵢ = a₁bᵢ + b₁aᵢ for i = 2, …, 7.” The coordinate i : Fin 7 represents the paper's coordinate i + 1. Finset.Ioi (0 : Fin 7) consists of indices 1 through 6.

**Definition 1.2 (The octonion clause of Remark 5.9).**

$$(\operatorname{claim}: \operatorname{Prop}) = (\exists \nu: (\operatorname{Fin}\left(7\right) \to \mathbb{R}) \to_{l}[\mathbb{R}] (\operatorname{D5.S3.VertexAlgebra.MonsterTwistedOctonionNorm.Octonion}), \exists \pi: (\operatorname{D5.S3.VertexAlgebra.MonsterTwistedOctonionNorm.Octonion}) \to_{l}[\mathbb{R}] (\operatorname{Fin}\left(7\right) \to \mathbb{R}), \forall a: \operatorname{Fin}\left(7\right) \to \mathbb{R}, \forall b: \operatorname{Fin}\left(7\right) \to \mathbb{R}, \operatorname{vidinliMul}\left(a, b\right) = \pi\left(\operatorname{D5.S3.VertexAlgebra.MonsterTwistedOctonionNorm.mul}\left(\nu\left(a\right), \nu\left(b\right)\right)\right))$$

*Formalization.* `D5/S3/HomologicalAlgebra/CoskunEdenVidinliOctonion.claim` (`✓ std3`).

*Citation.* O. Coşkun and A. Eden (2025). *Structure of Vidinli Algebras: Simple Nonassociative Jordan–Lie Algebras with Azumaya Properties*. DOI: [10.48550/arXiv.2511.09395](https://doi.org/10.48550/arXiv.2511.09395). URL: <https://arxiv.org/abs/2511.09395v1>.

*Commentary.*

Remark 5.9, p. 23: “By [5, Proposition 9], see also Section 3.1, the Vidinli multiplication in dimension three arises as a push-forward of quaternion multiplication. Whether a similar push-forward description exists for the exceptional Vidinli algebra V₇ in terms of the octonions, or more generally for V_{2^k−1} in relation to higher Cayley-Dickson algebras, remains an open question.” The proposition expresses the affirmative answer to the octonion clause: there are real-linear maps ν and π satisfying the product identity for every pair a, b. The octonions and their multiplication are the eight-coordinate signed Cayley–Dickson model MonsterTwistedOctonionNorm.Octonion and MonsterTwistedOctonionNorm.mul. Neither map is assumed to preserve products.

**Theorem 1.3 (The octonion clause has a negative answer).**

$$\neg (\exists \nu: (\operatorname{Fin}\left(7\right) \to \mathbb{R}) \to_{l}[\mathbb{R}] (\operatorname{D5.S3.VertexAlgebra.MonsterTwistedOctonionNorm.Octonion}), \exists \pi: (\operatorname{D5.S3.VertexAlgebra.MonsterTwistedOctonionNorm.Octonion}) \to_{l}[\mathbb{R}] (\operatorname{Fin}\left(7\right) \to \mathbb{R}), \forall a: \operatorname{Fin}\left(7\right) \to \mathbb{R}, \forall b: \operatorname{Fin}\left(7\right) \to \mathbb{R}, \operatorname{vidinliMul}\left(a, b\right) = \pi\left(\operatorname{D5.S3.VertexAlgebra.MonsterTwistedOctonionNorm.mul}\left(\nu\left(a\right), \nu\left(b\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/CoskunEdenVidinliOctonion.result` (`✓ std3`). ∎

*Resolves.* `Problems/coskun-eden-2025-vidinli-octonion-pushforward` (refuted) by `D5/S3/HomologicalAlgebra/CoskunEdenVidinliOctonion.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"coskun-eden-2025-vidinli-octonion-pushforward","declaration_gid":"D5/S3/HomologicalAlgebra/CoskunEdenVidinliOctonion.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* O. Coşkun and A. Eden (2025). *Structure of Vidinli Algebras: Simple Nonassociative Jordan–Lie Algebras with Azumaya Properties*. DOI: [10.48550/arXiv.2511.09395](https://doi.org/10.48550/arXiv.2511.09395). URL: <https://arxiv.org/abs/2511.09395v1>.

*Commentary.*

The right unit forces ν to be injective and π to be surjective. Rank-nullity gives a one-dimensional kernel for π. Left multiplication by the nonzero octonion ν(e₂) is injective by the multiplicative positive-definite square norm. The vectors e₂ + e₃, e₄, e₅, e₆, e₇ are independent and are killed by left multiplication by e₂ in the Vidinli algebra. Their images would therefore embed a five-dimensional real vector space into ker π, contradicting rank-nullity. Here e₂ in the paper is Pi.single 1 1 in the zero-based coordinates. The statement concerns arbitrary real-linear maps. It does not address the higher Cayley–Dickson clause, where zero divisors prevent this injectivity argument.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/CoskunEdenVidinliOctonion.claim`
- Truth anchor: `D5/S3/HomologicalAlgebra/CoskunEdenVidinliOctonion.result`
- Truth anchor: `D5/S3/HomologicalAlgebra/CoskunEdenVidinliOctonion.vidinliMul`
- Dependency: [D5/S3/VertexAlgebra/MonsterTwistedOctonionNorm](../VertexAlgebra/MonsterTwistedOctonionNorm.md)
