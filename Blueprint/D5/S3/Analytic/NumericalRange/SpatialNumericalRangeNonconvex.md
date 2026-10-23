# Dedania–Patel Spatial Numerical Range Convexity Refutation

## Abstract

A three-dimensional complex normed algebra has two spatial numerical range points whose midpoint is absent.

Dedania–Patel, arXiv:2306.16172v1, §1, p. 2, definition verbatim: “Let $S(A) = \{x\in A:\left\lVert x \right\rVert = 1\}$ be the unit sphere in $A$. Let $A^{*}$ be the Banach space dual of $A$. Let $D_{A}(x) = \{\varphi\in A^{*}:\left\lVert \varphi \right\rVert=1=\varphi(x)\}$ for each $x\in S(A)$. Further, let $V_{A}(a;x) = \{\varphi(ax):\varphi\in D_{A}(x)\}$ for $a\in A$ and $x\in S(A)$. Then $V_{A}(a) = \cup\{V_{A}(a;x):x\in S(A)\}$ is the spatial numerical range (SNR)”

**Definition 1.1 (Spatial numerical range).**

$$\forall A: \operatorname{Type}\left(\right), [\operatorname{NonUnitalNormedRing}\left(A\right)] [\operatorname{NormedSpace}\left(\mathbb{C}, A\right)] [\operatorname{IsScalarTower}\left(\mathbb{C}, A, A\right)] [\operatorname{SMulCommClass}\left(\mathbb{C}, A, A\right)], \forall a: A, \forall z: \mathbb{C}, z \in \operatorname{spatialNumericalRange}\left(a\right) \Leftrightarrow (\exists x: A, \Vert x\Vert = 1 \land \exists phi: \operatorname{ContinuousLinearMap}\left(\mathbb{C}, A, \mathbb{C}\right), \Vert phi\Vert = 1 \land \left(\operatorname{phi}\left(x\right) = 1 \land \operatorname{phi}\left(a*x\right) = z\right))$$

*Formalization.* `D5/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex.spatialNumericalRange` (`✓ std3`).

*Citation.* H. V. Dedania and A. B. Patel (2024). *Spatial numerical range in non-unital, normed algebras and their unitizations*. URL: <https://arxiv.org/abs/2306.16172v1>.

*Commentary.*

Formal encoding of the quoted definition: for a complex normed algebra A, spatialNumericalRange a consists of the values φ(a*x), where x is a unit vector and φ is a continuous complex-linear functional with norm one and φ(x)=1. The algebra has NonUnitalNormedRing, NormedSpace ℂ, IsScalarTower ℂ A A and SMulCommClass ℂ A A instances; convexity is over ℝ.

**Definition 1.2 (Universal spatial convexity).**

$$claim \Leftrightarrow (\forall A: \operatorname{Type}\left(\right), [\operatorname{NonUnitalNormedRing}\left(A\right)] [\operatorname{NormedSpace}\left(\mathbb{C}, A\right)] [\operatorname{IsScalarTower}\left(\mathbb{C}, A, A\right)] [\operatorname{SMulCommClass}\left(\mathbb{C}, A, A\right)], \forall a: A, \operatorname{Convex}\left(\mathbb{R}, \operatorname{spatialNumericalRange}\left(a\right)\right))$$

*Formalization.* `D5/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex.claim` (`✓ std3`).

*Citation.* H. V. Dedania and A. B. Patel (2024). *Spatial numerical range in non-unital, normed algebras and their unitizations*. URL: <https://arxiv.org/abs/2306.16172v1>.

*Commentary.*

Dedania and Patel ask in Section 1, page 2: “It is still open problem wether V_A(a) is always convex? This problem is discussed in [5].” The formal claim quantifies over every complex normed algebra with the four indicated instances and every element a, and asserts Convex ℝ (spatialNumericalRange a). It assumes neither completeness nor commutativity.

**Theorem 1.3 (An absent midpoint).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex.result` (`✓ std3`). ∎

*Resolves.* `Problems/dedania-patel-2024-spatial-numerical-range-convexity` (refuted) by `D5/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dedania-patel-2024-spatial-numerical-range-convexity","declaration_gid":"D5/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* H. V. Dedania and A. B. Patel (2024). *Spatial numerical range in non-unital, normed algebras and their unitizations*. URL: <https://arxiv.org/abs/2306.16172v1>.

*Commentary.*

Let P=(1/5)[[1,2],[2,4]] and give ℂ⊕ℂ² the product (α,x)(β,y)=(αβ,αPy+βx) and norm max(3|α|,‖x‖∞). The Lean coordinates use u₀=3α and e=(3,0). Idempotence of P gives associativity, and the multiplication is submultiplicative. The two norming pairs with vectors (0,(1,i)) and (0,(i,1)) and coordinate functionals give z₁=1/5+2i/5 and z₂=4/5+2i/5. For any norm-one functional, the sum of coefficient norms is at most one. The norming equation makes the diagonal products real; attaining imaginary height 2/5 forces the cross products to be purely imaginary. At the midpoint 1/2+2i/5 both coefficient norms would be 1/2, contradicting the identity between the products of the diagonal and cross terms. Thus the midpoint is absent and the universal convexity assertion is false.

## References

- Truth anchor: `D5/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex.claim`
- Truth anchor: `D5/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex.result`
- Truth anchor: `D5/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex.spatialNumericalRange`
