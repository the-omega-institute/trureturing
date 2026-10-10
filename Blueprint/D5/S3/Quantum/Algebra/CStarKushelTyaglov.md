# CStarKushelTyaglov

## Abstract

A cubic polynomial over two by two complex matrices refutes Krishna’s C*-algebraic conjecture.

**Definition 1.1 (Krishna’s Conjecture 2.4).**

$$claimKushelTyaglov \Leftrightarrow \forall A : Type, [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall d : \mathbb{N}, (2 \le d) \Rightarrow \forall a : \operatorname{Fin}\left(d\right) \to A, \forall b : \operatorname{Fin}\left(d - 1\right) \to A, (\forall z : A, \sum_{j:\operatorname{Fin}\left(d\right)}(\operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{eraseIdx}\left(\operatorname{List}.\operatorname{ofFn}\left((i:\operatorname{Fin}\left(d\right)) \mapsto z - a\left(i\right)\right), \operatorname{val}\left(j\right)\right)\right)) = (d) \cdot (\operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{ofFn}\left((k:\operatorname{Fin}\left(d - 1\right)) \mapsto z - b\left(k\right)\right)\right))) \Rightarrow \operatorname{let} S=\sum_{j:\operatorname{Fin}\left(d\right)}(a\left(j\right)); \operatorname{let} T=\sum_{j:\operatorname{Fin}\left(d\right)}((a\left(j\right))^{2}) - (\frac{1}{(d:\mathbb{C})^{2}}) \cdot ((S)^{2}); (\sum_{k:\operatorname{Fin}\left(d - 1\right)}((b\left(k\right) \cdot \operatorname{star}\left(b\left(k\right)\right))^{2}) \le (\frac{(d:\mathbb{C}) - 6}{(d:\mathbb{C})}) \cdot (\sum_{j:\operatorname{Fin}\left(d\right)}((a\left(j\right) \cdot \operatorname{star}\left(a\left(j\right)\right))^{2})) + (\frac{1}{(d:\mathbb{C})^{2}}) \cdot ((\sum_{j:\operatorname{Fin}\left(d\right)}(a\left(j\right) \cdot \operatorname{star}\left(a\left(j\right)\right)))^{2}) + (\frac{1}{(d:\mathbb{C})^{2}}) \cdot (T \cdot \operatorname{star}\left(T\right)) + (\frac{2}{(d:\mathbb{C})^{1}}) \cdot (\sum_{j:\operatorname{Fin}\left(d\right)}(a\left(j\right) \cdot \left(a\left(j\right) + (\frac{1}{(d:\mathbb{C})^{1}}) \cdot (S)\right) \cdot \operatorname{star}\left(a\left(j\right) + (\frac{1}{(d:\mathbb{C})^{1}}) \cdot (S)\right) \cdot \operatorname{star}\left(a\left(j\right)\right))) - (\frac{4}{(d:\mathbb{C})^{3}}) \cdot (\sum_{j:\operatorname{Fin}\left(d\right)}(a\left(j\right) \cdot S \cdot \operatorname{star}\left(S\right) \cdot \operatorname{star}\left(a\left(j\right)\right)))) \land (\sum_{k:\operatorname{Fin}\left(d - 1\right)}((\operatorname{star}\left(b\left(k\right)\right) \cdot b\left(k\right))^{2}) \le (\frac{(d:\mathbb{C}) - 6}{(d:\mathbb{C})}) \cdot (\sum_{j:\operatorname{Fin}\left(d\right)}((\operatorname{star}\left(a\left(j\right)\right) \cdot a\left(j\right))^{2})) + (\frac{1}{(d:\mathbb{C})^{2}}) \cdot ((\sum_{j:\operatorname{Fin}\left(d\right)}(\operatorname{star}\left(a\left(j\right)\right) \cdot a\left(j\right)))^{2}) + (\frac{1}{(d:\mathbb{C})^{2}}) \cdot (\operatorname{star}\left(T\right) \cdot T) + (\frac{2}{(d:\mathbb{C})^{1}}) \cdot (\sum_{j:\operatorname{Fin}\left(d\right)}(\operatorname{star}\left(a\left(j\right)\right) \cdot \operatorname{star}\left(a\left(j\right) + (\frac{1}{(d:\mathbb{C})^{1}}) \cdot (S)\right) \cdot \left(a\left(j\right) + (\frac{1}{(d:\mathbb{C})^{1}}) \cdot (S)\right) \cdot a\left(j\right))) - (\frac{4}{(d:\mathbb{C})^{3}}) \cdot (\sum_{j:\operatorname{Fin}\left(d\right)}(\operatorname{star}\left(a\left(j\right)\right) \cdot \operatorname{star}\left(S\right) \cdot S \cdot a\left(j\right))))$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarKushelTyaglov.claimKushelTyaglov` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2022). *C*-algebraic Schoenberg Conjecture*. DOI: [10.48550/arXiv.2206.06653](https://doi.org/10.48550/arXiv.2206.06653). URL: <https://arxiv.org/abs/2206.06653v1>.

*Commentary.*

Conjecture 2.4 (C*-algebraic Kushel-Tyaglov Conjecture), pp. 3–4: “Let 𝒜 be a C*-algebra, n∈ℕ\{1} and let P(z) ≔ (z−a₁)(z−a₂)⋯(z−a_d) be a polynomial over 𝒜 with a₁, a₂, …, a_d ∈ 𝒜. Assume that P′ can be written as P′(z) ≔ d(z−b₁)⋯(z−b_{d−1}) on 𝒜 with b₁, b₂, …, b_{d−1} ∈ 𝒜. Then” the two inequalities displayed below. The printed n is read as d throughout. The encoding uses zero-based Fin d and Fin (d−1), complex scalar multiplication, star and the C*-order. It restricts the source to d≥2 and unital C*-algebras in Type with PartialOrder and StarOrderedRing; this weakens the assertion, so its negation refutes the source statement.

**Theorem 1.2 (The conjecture is false).**

$$\neg claimKushelTyaglov$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CStarKushelTyaglov.result` (`✓ std3`). ∎

*Resolves.* `Problems/krishna-2022-cstar-kushel-tyaglov` (refuted) by `D5/S3/Quantum/Algebra/CStarKushelTyaglov.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"krishna-2022-cstar-kushel-tyaglov","declaration_gid":"D5/S3/Quantum/Algebra/CStarKushelTyaglov.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Schoenberg Conjecture*. DOI: [10.48550/arXiv.2206.06653](https://doi.org/10.48550/arXiv.2206.06653). URL: <https://arxiv.org/abs/2206.06653v1>.

*Commentary.*

At degree three the matrices a and b satisfy the factorization hypothesis. The first inequality has right side minus left side equal to −67/27 times Matrix.single 0 0 1. Its first diagonal entry is negative, contradicting the C*-order.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/CStarKushelTyaglov.claimKushelTyaglov`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarKushelTyaglov.result`
- Dependency: [D5/S3/Quantum/Algebra/CStarSchoenberg](CStarSchoenberg.md)
