# CStarDualMeanValue

## Abstract

A cubic in the product of two complex fields refutes the dual mean value bound.

**Definition 1.1 (The ordered polynomial).**

$$\forall A : Type, [\operatorname{Ring}\left(A\right)] \forall d : \mathbb{N}, \forall a : \operatorname{Fin}\left(d\right) \to A, \forall z : A, \operatorname{orderedPoly}\left(a, z\right) = \operatorname{List}.\operatorname{prod}\left((\operatorname{List}.\operatorname{ofFn}\left(((i:\operatorname{Fin}\left(d\right)) \mapsto z - a\left(i\right))\right))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarDualMeanValue.orderedPoly` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2022). *C*-algebraic Smale Mean Value Conjecture and Dubinin-Sugawa Dual Mean Value Conjecture*. DOI: [10.48550/arXiv.2206.08154](https://doi.org/10.48550/arXiv.2206.08154). URL: <https://arxiv.org/abs/2206.08154v1>.

*Commentary.*

Section 2, p. 4: “Let 𝒜 be a C*-algebra. For P(z) ≔ (z−a₁)(z−a₂)⋯(z−aₙ) for all z∈𝒜 with a₁, a₂, …, aₙ ∈ 𝒜, we define P′(z)=∑ⱼ₌₁ⁿ (z−a₁)⋯(z−aⱼ)̂⋯(z−aₙ), ∀z∈𝒜 where the term with cap is missing.” The polynomial preserves the factor order through List.ofFn and List.prod. The indices are zero-based Fin d. The ordered derivative is CStarSchoenberg.orderedDeriv, with the omitted factor removed by List.eraseIdx.

**Definition 1.2 (The C*-algebraic dual mean value conjecture).**

$$\operatorname{claim} = (\forall A : Type, [\operatorname{CommCStarAlgebra}\left(A\right)] \forall n : \mathbb{N}, (2 \le n) \Rightarrow (\forall a : \operatorname{Fin}\left(n\right) \to A, \forall z : A, (\operatorname{CStarSchoenberg}.\operatorname{orderedDeriv}\left(a, z\right) \ne 0) \Rightarrow (\exists w : A, (\operatorname{CStarSchoenberg}.\operatorname{orderedDeriv}\left(a, w\right) = 0) \land (\frac{\left\lVert \operatorname{CStarSchoenberg}.\operatorname{orderedDeriv}\left(a, z\right) \right\rVert}{(n:\mathbb{R})} \le \frac{\left\lVert \operatorname{orderedPoly}\left(a, z\right) - \operatorname{orderedPoly}\left(a, w\right) \right\rVert}{\left\lVert z - w \right\rVert}))))$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarDualMeanValue.claim` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2022). *C*-algebraic Smale Mean Value Conjecture and Dubinin-Sugawa Dual Mean Value Conjecture*. DOI: [10.48550/arXiv.2206.08154](https://doi.org/10.48550/arXiv.2206.08154). URL: <https://arxiv.org/abs/2206.08154v1>.

*Commentary.*

Conjecture DUALSMALE (Conjecture 3.1), Section 3, p. 7: “Let 𝒜 be a commutative C*-algebra. Let P(z) ≔ (z−a₁)⋯(z−aₙ) be a polynomial of degree n ≥ 2 over 𝒜, a₁, …, aₙ ∈ 𝒜. If z∈𝒜 is not a critical point of P, then there exists a critical point w∈𝒜 of P such that ‖P′(z)‖/deg(P) = ‖P′(z)‖/n ≤ ‖P(z)−P(w)‖/‖z−w‖.” The roots a use zero-based Fin n indices. Noncritical means CStarSchoenberg.orderedDeriv a z ≠ 0, as in the source's gloss in Section 2; critical means CStarSchoenberg.orderedDeriv a w = 0. The degree n is cast to ℝ. CommCStarAlgebra restricts A to unital commutative C*-algebras in Type, weakening the universal assertion, so a counterexample in this subclass refutes the source statement.

**Theorem 1.3 (The norm-form conjecture is false).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CStarDualMeanValue.result` (`✓ std3`). ∎

*Resolves.* `Problems/krishna-2022-cstar-dubinin-sugawa-dual-mean-value` (refuted) by `D5/S3/Quantum/Algebra/CStarDualMeanValue.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"krishna-2022-cstar-dubinin-sugawa-dual-mean-value","declaration_gid":"D5/S3/Quantum/Algebra/CStarDualMeanValue.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Smale Mean Value Conjecture and Dubinin-Sugawa Dual Mean Value Conjecture*. DOI: [10.48550/arXiv.2206.08154](https://doi.org/10.48550/arXiv.2206.08154). URL: <https://arxiv.org/abs/2206.08154v1>.

*Commentary.*

Take A = ℂ × ℂ, n = 3, z = (0,0) and roots (0,3/2), (3,3/2), (3,3/2). The polynomial is (x(x−3)²,(y−3/2)³), and its ordered derivative is (3(x−1)(x−3),3(y−3/2)²). The only critical points are (1,3/2) and (3,3/2). At z = 0 the derivative is (9,27/4), whose supremum norm is 9. The two difference quotients are 8/3 and 9/8, both strictly below the required threshold 3. At the first critical point the second coordinate enlarges the denominator from 1 to 3/2 while the numerator norm remains 4; at the second the first coordinate contributes zero to the polynomial difference. Thus the scalar lower bound fails to pass to the supremum norm on products. The source's degree-two theorem remains intact.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/CStarDualMeanValue.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarDualMeanValue.orderedPoly`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarDualMeanValue.result`
- Dependency: [D5/S3/Quantum/Algebra/CStarSchoenberg](CStarSchoenberg.md)
