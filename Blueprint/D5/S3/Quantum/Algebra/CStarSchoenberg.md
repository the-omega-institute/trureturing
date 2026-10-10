# CStarSchoenberg

## Abstract

A cubic polynomial over two by two complex matrices refutes Krishna’s C*-algebraic conjecture.

**Definition 1.1 (The ordered derivative).**

$$\forall A : Type, [\operatorname{Ring}\left(A\right)] \forall d : \mathbb{N}, \forall a : \operatorname{Fin}\left(d\right) \to A, \forall z : A, \operatorname{orderedDeriv}\left(a, z\right) = \sum_{j:\operatorname{Fin}\left(d\right)}(\operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{eraseIdx}\left(\operatorname{List}.\operatorname{ofFn}\left((i:\operatorname{Fin}\left(d\right)) \mapsto z - a\left(i\right)\right), \operatorname{val}\left(j\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSchoenberg.orderedDeriv` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2022). *C*-algebraic Schoenberg Conjecture*. DOI: [10.48550/arXiv.2206.06653](https://doi.org/10.48550/arXiv.2206.06653). URL: <https://arxiv.org/abs/2206.06653v1>.

*Commentary.*

Section 2, p. 2: “Let 𝒜 be a C*-algebra. Given P(z) ≔ (z−a₁)(z−a₂)⋯(z−a_d) for all z∈𝒜 with a₁, a₂, …, a_d ∈ 𝒜, we define P′(z)=∑_{j=1}^d (z−a₁)⋯(z−aⱼ)̂⋯(z−a_d), ∀z∈𝒜 where the term with cap is missing.” List.eraseIdx removes the j-th factor, preserving the order of the other factors. Its index is the natural number val(j).

**Definition 1.2 (Factorization on the entire algebra).**

$$\forall A : Type, [\operatorname{Ring}\left(A\right)] \forall d : \mathbb{N}, \forall a : \operatorname{Fin}\left(d\right) \to A, \forall b : \operatorname{Fin}\left(d - 1\right) \to A, \operatorname{DerivFactors}\left(d, a, b\right) \Leftrightarrow \forall z : A, \operatorname{orderedDeriv}\left(a, z\right) = (d) \cdot (\operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{ofFn}\left((k:\operatorname{Fin}\left(d - 1\right)) \mapsto z - b\left(k\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSchoenberg.DerivFactors` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2022). *C*-algebraic Schoenberg Conjecture*. DOI: [10.48550/arXiv.2206.06653](https://doi.org/10.48550/arXiv.2206.06653). URL: <https://arxiv.org/abs/2206.06653v1>.

*Commentary.*

Conjecture 2.1, p. 2: “If P′ can be written as P′(z)=d(z−b₁)(z−b₂)⋯(z−b_{d−1}) on 𝒜 with b₁, b₂, …, b_{d−1} ∈ 𝒜”. The equality is required for every z in A. The scalar d acts by natural repeated addition.

**Definition 1.3 (The second matrix in the example).**

$$y:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right) = (\operatorname{Matrix}.\operatorname{single}\left(0, 0, (1:\mathbb{C})\right):\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)) + (\operatorname{Matrix}.\operatorname{single}\left(0, 1, (1:\mathbb{C})\right):\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSchoenberg.y` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Schoenberg Conjecture*. DOI: [10.48550/arXiv.2206.06653](https://doi.org/10.48550/arXiv.2206.06653). URL: <https://arxiv.org/abs/2206.06653v1>.

*Commentary.*

The matrix units use zero-based indices. Thus y has first row (1,1) and second row (0,0).

**Definition 1.4 (The three polynomial factors).**

$$a:\operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right) = ![(\frac{1}{(3:\mathbb{C})}) \cdot ((2) \cdot ((\operatorname{Matrix}.\operatorname{single}\left(0, 1, (1:\mathbb{C})\right):\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))) + y), (\frac{1}{(3:\mathbb{C})}) \cdot (-(\operatorname{Matrix}.\operatorname{single}\left(0, 1, (1:\mathbb{C})\right):\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)) + y), (\frac{1}{(3:\mathbb{C})}) \cdot (-(\operatorname{Matrix}.\operatorname{single}\left(0, 1, (1:\mathbb{C})\right):\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)) - (2) \cdot (y))]$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSchoenberg.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Schoenberg Conjecture*. DOI: [10.48550/arXiv.2206.06653](https://doi.org/10.48550/arXiv.2206.06653). URL: <https://arxiv.org/abs/2206.06653v1>.

*Commentary.*

The three entries sum to zero. The matrix Matrix.single 0 1 1 is the off-diagonal matrix unit.

**Definition 1.5 (A critical point).**

$$u:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right) = (\frac{1}{(3:\mathbb{C})}) \cdot ((\operatorname{Matrix}.\operatorname{single}\left(0, 1, (1:\mathbb{C})\right):\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)) + y)$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSchoenberg.u` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Schoenberg Conjecture*. DOI: [10.48550/arXiv.2206.06653](https://doi.org/10.48550/arXiv.2206.06653). URL: <https://arxiv.org/abs/2206.06653v1>.

*Commentary.*

This matrix and its negative are the two ordered derivative factors.

**Definition 1.6 (The two derivative factors).**

$$b:\operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right) = ![u,-u]$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSchoenberg.b` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Schoenberg Conjecture*. DOI: [10.48550/arXiv.2206.06653](https://doi.org/10.48550/arXiv.2206.06653). URL: <https://arxiv.org/abs/2206.06653v1>.

*Commentary.*

The Fin 2 tuple is (u,−u).

**Lemma 1.7 (The factor sum vanishes).**

$$\sum_{j:\operatorname{Fin}\left(3\right)}(a\left(j\right)) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CStarSchoenberg.sum_a` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Schoenberg Conjecture*. DOI: [10.48550/arXiv.2206.06653](https://doi.org/10.48550/arXiv.2206.06653). URL: <https://arxiv.org/abs/2206.06653v1>.

*Commentary.*

The entries of the three matrices cancel.

**Lemma 1.8 (The ordered derivative factors for every matrix).**

$$\operatorname{DerivFactors}\left(3, a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CStarSchoenberg.factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Schoenberg Conjecture*. DOI: [10.48550/arXiv.2206.06653](https://doi.org/10.48550/arXiv.2206.06653). URL: <https://arxiv.org/abs/2206.06653v1>.

*Commentary.*

Entrywise multiplication for an arbitrary complex two by two matrix gives the factorization, without assuming the variable commutes with the factors.

**Lemma 1.9 (A negative diagonal entry excludes positivity).**

$$\forall c : \mathbb{R}, (c < 0) \Rightarrow \left(\neg \operatorname{Matrix}.\operatorname{PosSemidef}\left(((c:\mathbb{C})) \cdot ((\operatorname{Matrix}.\operatorname{single}\left(0, 0, (1:\mathbb{C})\right):\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CStarSchoenberg.negative_e11_not_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Schoenberg Conjecture*. DOI: [10.48550/arXiv.2206.06653](https://doi.org/10.48550/arXiv.2206.06653). URL: <https://arxiv.org/abs/2206.06653v1>.

*Commentary.*

A positive-semidefinite matrix has nonnegative diagonal entries. The first diagonal entry is the real number c.

**Definition 1.10 (Krishna’s Conjecture 2.1).**

$$claimSchoenberg \Leftrightarrow \forall A : Type, [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall d : \mathbb{N}, (2 \le d) \Rightarrow \forall a : \operatorname{Fin}\left(d\right) \to A, \forall b : \operatorname{Fin}\left(d - 1\right) \to A, (\forall z : A, \sum_{j:\operatorname{Fin}\left(d\right)}(\operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{eraseIdx}\left(\operatorname{List}.\operatorname{ofFn}\left((i:\operatorname{Fin}\left(d\right)) \mapsto z - a\left(i\right)\right), \operatorname{val}\left(j\right)\right)\right)) = (d) \cdot (\operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{ofFn}\left((k:\operatorname{Fin}\left(d - 1\right)) \mapsto z - b\left(k\right)\right)\right))) \Rightarrow \left((\sum_{k:\operatorname{Fin}\left(d - 1\right)}(b\left(k\right) \cdot \operatorname{star}\left(b\left(k\right)\right)) \le (\frac{1}{(d:\mathbb{C})^{2}}) \cdot (\sum_{j:\operatorname{Fin}\left(d\right)}(a\left(j\right)) \cdot \operatorname{star}\left(\sum_{j:\operatorname{Fin}\left(d\right)}(a\left(j\right))\right)) + (\frac{(d:\mathbb{C}) - 2}{(d:\mathbb{C})}) \cdot (\sum_{j:\operatorname{Fin}\left(d\right)}(a\left(j\right) \cdot \operatorname{star}\left(a\left(j\right)\right)))) \land (\sum_{k:\operatorname{Fin}\left(d - 1\right)}(\operatorname{star}\left(b\left(k\right)\right) \cdot b\left(k\right)) \le (\frac{1}{(d:\mathbb{C})^{2}}) \cdot (\operatorname{star}\left(\sum_{j:\operatorname{Fin}\left(d\right)}(a\left(j\right))\right) \cdot \sum_{j:\operatorname{Fin}\left(d\right)}(a\left(j\right))) + (\frac{(d:\mathbb{C}) - 2}{(d:\mathbb{C})}) \cdot (\sum_{j:\operatorname{Fin}\left(d\right)}(\operatorname{star}\left(a\left(j\right)\right) \cdot a\left(j\right))))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSchoenberg.claimSchoenberg` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2022). *C*-algebraic Schoenberg Conjecture*. DOI: [10.48550/arXiv.2206.06653](https://doi.org/10.48550/arXiv.2206.06653). URL: <https://arxiv.org/abs/2206.06653v1>.

*Commentary.*

Conjecture 2.1 (C*-algebraic Schoenberg Conjecture), pp. 2–3: “Let 𝒜 be a C*-algebra. Let d∈ℕ\{1}, P(z) ≔ (z−a₁)(z−a₂)⋯(z−a_d) be a polynomial over 𝒜 with a₁, a₂, …, a_d ∈ 𝒜. If P′ can be written as P′(z)=d(z−b₁)(z−b₂)⋯(z−b_{d−1}) on 𝒜 with b₁, b₂, …, b_{d−1} ∈ 𝒜, then” the two inequalities displayed below. The encoding uses zero-based Fin d and Fin (d−1), complex scalar multiplication, star and the C*-order. It restricts the source to d≥2 and unital C*-algebras in Type with PartialOrder and StarOrderedRing; this weakens the assertion, so its negation refutes the source statement.

**Theorem 1.11 (The conjecture is false).**

$$\neg claimSchoenberg$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CStarSchoenberg.result` (`✓ std3`). ∎

*Resolves.* `Problems/krishna-2022-cstar-schoenberg` (refuted) by `D5/S3/Quantum/Algebra/CStarSchoenberg.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"krishna-2022-cstar-schoenberg","declaration_gid":"D5/S3/Quantum/Algebra/CStarSchoenberg.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Schoenberg Conjecture*. DOI: [10.48550/arXiv.2206.06653](https://doi.org/10.48550/arXiv.2206.06653). URL: <https://arxiv.org/abs/2206.06653v1>.

*Commentary.*

At degree three the matrices a and b satisfy the factorization hypothesis. The first inequality has right side minus left side equal to −2/9 times Matrix.single 0 0 1. Its first diagonal entry is negative, contradicting the C*-order.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/CStarSchoenberg.DerivFactors`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSchoenberg.a`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSchoenberg.b`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSchoenberg.claimSchoenberg`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSchoenberg.factorization`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSchoenberg.negative_e11_not_posSemidef`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSchoenberg.orderedDeriv`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSchoenberg.result`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSchoenberg.sum_a`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSchoenberg.u`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSchoenberg.y`
