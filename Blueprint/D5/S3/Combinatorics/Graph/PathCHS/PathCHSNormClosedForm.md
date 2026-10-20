# PathCHSNormClosedForm

## Abstract

Complete homogeneous symmetric functions of finite path spectra.

**Theorem 1.1 (The path matrix is Hermitian).**

$$\forall n \in \mathbb{N},\; \operatorname{Matrix}.\operatorname{IsHermitian}\left(\operatorname{Matrix}.\operatorname{of}\left(\operatorname{fun} (i:\operatorname{Fin}\left(n\right)) \mapsto \operatorname{fun} (j:\operatorname{Fin}\left(n\right)) \mapsto \operatorname{if} (((i:\mathbb{N}) + 1 = (j:\mathbb{N})) \lor ((j:\mathbb{N}) + 1 = (i:\mathbb{N}))) \operatorname{then} (1:\mathbb{R}) \operatorname{else} 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.pathAdjHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

The entry with indices i and j equals the entry with indices j and i. The matrix is the adjacency matrix of the path with vertices Fin n.

**Definition 1.2 (Complete homogeneous symmetric value).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{chs}\left(n, d\right) = \operatorname{MvPolynomial}.\operatorname{eval}\left(\operatorname{Matrix}.\operatorname{IsHermitian}.\operatorname{eigenvalues}\left(\operatorname{pathAdjHermitian}\left(n\right)\right), \operatorname{MvPolynomial}.\operatorname{hsymm}\left(\operatorname{Fin}\left(n\right), \mathbb{R}, d\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.chs` (`✓ std3`).

*Citation.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

Page 2, Equation (1.1): “∑_{d=0}^{∞} h_d(x₁, x₂, …, x_n) t^d = ∏_{i=1}^{n} 1/(1 − x_i t).” The polynomial hsymm is evaluated at the real eigenvalues of the path adjacency matrix.

**Definition 1.3 (The complete homogeneous symmetric norm).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{chsNorm}\left(n, d\right) = \operatorname{chs}\left(n, d\right)^{\frac{(1:\mathbb{R})}{(d:\mathbb{R})}}$$

*Formalization.* `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.chsNorm` (`✓ std3`).

*Citation.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

Page 2, Theorem 1.4: “Suppose d ≥ 2 is even. The following function defines a norm on H_n: ‖A‖_d = h_d(λ₁, λ₂, …, λ_n)^{1/d}.” Natural d is cast to ℝ in the reciprocal exponent.

**Definition 1.4 (Finite second-difference expression).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{pathFormula}\left(n, m\right) = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(\operatorname{Nat}.\operatorname{div}\left(m, n + 1\right) + 1\right)} ((\operatorname{D5}.\operatorname{S0}.\operatorname{Conventions}.\operatorname{IntegerIndexBinomial}.\operatorname{binom}\left(2 \cdot m + n - 1, (m:\mathbb{Z}) - (k:\mathbb{Z}) \cdot \left((n:\mathbb{Z}) + 1\right)\right):\mathbb{Z}) - 2 \cdot (\operatorname{D5}.\operatorname{S0}.\operatorname{Conventions}.\operatorname{IntegerIndexBinomial}.\operatorname{binom}\left(2 \cdot m + n - 1, (m:\mathbb{Z}) - (k:\mathbb{Z}) \cdot \left((n:\mathbb{Z}) + 1\right) - 1\right):\mathbb{Z}) + (\operatorname{D5}.\operatorname{S0}.\operatorname{Conventions}.\operatorname{IntegerIndexBinomial}.\operatorname{binom}\left(2 \cdot m + n - 1, (m:\mathbb{Z}) - (k:\mathbb{Z}) \cdot \left((n:\mathbb{Z}) + 1\right) - 2\right):\mathbb{Z}))$$

*Formalization.* `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.pathFormula` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

The upper index is 2m+n−1. Nat.div is natural-number quotient. Each binomial value is cast to ℤ before subtraction.

**Definition 1.5 (Problem 1 for path norms).**

$$\operatorname{claim} = \left(\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; (1 \le n) \to (2 \le m) \to (\operatorname{chs}\left(n, 2 \cdot m\right) = (\operatorname{pathFormula}\left(n, m\right):\mathbb{R})) \land (\operatorname{chsNorm}\left(n, 2 \cdot m\right) = (\operatorname{pathFormula}\left(n, m\right):\mathbb{R})^{\frac{(1:\mathbb{R})}{(2 \cdot m:\mathbb{R})}})\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

Page 14, Section 5, Problem 1: “The path of order n has m = n − 1 edges. Proposition 5.14 (a) therefore implies that ‖P_n‖₂ = √(n − 1). However, computing ‖P_n‖_d for d ≥ 4 seems unattainable at the moment. We leave this is an interesting open problem. Problem 1. Compute ‖P_n‖_d for d ≥ 4.” Here n ≥ 1 and d=2m with m ≥ 2; both the symmetric polynomial and its real root are specified.

**Theorem 1.6 (A geometric series times its denominator).**

$$\forall R \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] \forall a \in R,\; \operatorname{PowerSeries}.\operatorname{mk}\left(\operatorname{fun} (k:\mathbb{N}) \mapsto a^{k}\right) \cdot (1 - \operatorname{PowerSeries}.\operatorname{C}\left(a\right) \cdot \operatorname{PowerSeries}.\operatorname{X}) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.geometric_mul_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

Rescaling the geometric series gives the inverse of 1−aX over any commutative ring.

**Theorem 1.7 (The symmetric-polynomial generating function).**

$$\forall I \in \operatorname{Type},\; \forall R \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{CommRing}\left(R\right)] \forall a \in I \to R,\; \operatorname{PowerSeries}.\operatorname{mk}\left(\operatorname{fun} (d:\mathbb{N}) \mapsto \operatorname{MvPolynomial}.\operatorname{eval}\left(a, \operatorname{MvPolynomial}.\operatorname{hsymm}\left(I, R, d\right)\right)\right) \cdot \prod_{i:I} (1 - \operatorname{PowerSeries}.\operatorname{C}\left(a\left(i\right)\right) \cdot \operatorname{PowerSeries}.\operatorname{X}) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.hsymm_series_product` (`✓ std3`). ∎

*Citation.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

Equation (1.1), page 2, gives the generating function. Grouping monomials by total degree gives the reciprocal product of the linear factors over a commutative ring.

**Theorem 1.8 (Ring homomorphisms and constant-weight continuants).**

$$\forall R \in \operatorname{Type},\; \forall S \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] [\operatorname{CommRing}\left(S\right)] \forall f \in R \to +* S,\; \forall x \in R,\; \forall n \in \mathbb{N},\; f\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{NarayanaStrip}.\operatorname{CiglerStripProductAlgebra}.\operatorname{cont}\left(\operatorname{Function}.\operatorname{const}\left(\mathbb{N}, x\right), 1, 1, n\right)\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{NarayanaStrip}.\operatorname{CiglerStripProductAlgebra}.\operatorname{cont}\left(\operatorname{Function}.\operatorname{const}\left(\mathbb{N}, f\left(x\right)\right), 1, 1, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.continuant_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

A ring homomorphism preserves the initial values and the second-order recurrence.

**Theorem 1.9 (The zero-weight continuant).**

$$\forall R \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] \forall n \in \mathbb{N},\; \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{NarayanaStrip}.\operatorname{CiglerStripProductAlgebra}.\operatorname{cont}\left(\operatorname{Function}.\operatorname{const}\left(\mathbb{N}, (0:R)\right), 1, 1, n\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.continuant_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

At zero weight every term of the continuant is one.

**Theorem 1.10 (The reciprocal path continuant).**

$$\forall n \in \mathbb{N},\; \operatorname{PowerSeries}.\operatorname{mk}\left(\operatorname{fun} (d:\mathbb{N}) \mapsto \operatorname{chs}\left(n, d\right)\right) \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{NarayanaStrip}.\operatorname{CiglerStripProductAlgebra}.\operatorname{cont}\left(\operatorname{Function}.\operatorname{const}\left(\mathbb{N}, (\operatorname{PowerSeries}.\operatorname{X}:\operatorname{PowerSeries}\left(\mathbb{R}\right))^{2}\right), 1, 1, n\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.path_hsymm_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

The product over adjacency eigenvalues is the path determinant. Its reciprocal generates the symmetric polynomials.

**Theorem 1.11 (Even-degree values).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{chs}\left(n, 2 \cdot m\right) = (\operatorname{pathFormula}\left(n, m\right):\mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.chs_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For x(1+q)²=q, the recurrence identity (1+q)ⁿ cont(x;1,1;n)(1−q)=1−qⁿ⁺¹ holds at every order n. It supplies the reciprocal-continuant substitution; the Catalan coefficient transform then gives a binomial second difference and a geometric series of reflections.

**Theorem 1.12 (Closed form for every even path norm).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; (1 \le n) \to (2 \le m) \to (\operatorname{chs}\left(n, 2 \cdot m\right) = (\operatorname{pathFormula}\left(n, m\right):\mathbb{R})) \land (\operatorname{chsNorm}\left(n, 2 \cdot m\right) = (\operatorname{pathFormula}\left(n, m\right):\mathbb{R})^{\frac{(1:\mathbb{R})}{(2 \cdot m:\mathbb{R})}})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.result` (`✓ std3`). ∎

*Resolves.* `Problems/chavez-2023-path-chs-norm-closed-form` (proved) by `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chavez-2023-path-chs-norm-closed-form","declaration_gid":"D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

The second-difference expression gives the complete homogeneous symmetric value and hence its real root.

**Theorem 1.13 (Degree of the monic Chebyshev polynomial).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall n \in \mathbb{N},\; \operatorname{Polynomial}.\operatorname{natDegree}\left(\operatorname{Polynomial}.\operatorname{Chebyshev}.\operatorname{S}\left(K, (n:\mathbb{Z})\right)\right) = n$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.chebS_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

The identity with the second-kind Chebyshev polynomial after scaling the variable gives degree n.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.chebS_degree`
- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.chs`
- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.chsNorm`
- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.chs_formula`
- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.continuant_map`
- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.continuant_zero`
- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.geometric_mul_linear`
- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.hsymm_series_product`
- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.pathAdjHermitian`
- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.pathFormula`
- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.path_hsymm_series`
- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.result`
- Dependency: [D5/S0/Conventions/IntegerIndexBinomial](../../../../S0/Conventions/IntegerIndexBinomial.md)
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](../../../../S1/Recurrence/Invariants/CompositionalIterateCongruence.md)
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductContinuants](../../NarayanaStrip/CiglerStripProductContinuants.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge](../../Nonnesting/CatalanLagrangeBridge.md)
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../../../Quantum/FockSpace/ForbiddenNeighbourDeterminant.md)
