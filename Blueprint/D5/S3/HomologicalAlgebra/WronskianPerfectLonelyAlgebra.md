# Perfect polynomial extensions for complete Wronskians

## Abstract

A perfect homogeneous one-generator polynomial extension exists exactly at differential order one.

**Definition 1.1 (The differential multi-indices).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(k: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.I}\left(d, k\right): \operatorname{Finset}\left(\operatorname{Finsupp}\left(\operatorname{Fin}\left(d\right), \mathbb{N}\right)\right)\right) = \{\left(\alpha: \operatorname{Finsupp}\left(\operatorname{Fin}\left(d\right), \mathbb{N}\right)\right) \mid \operatorname{Finsupp.degree}\left(\alpha\right) \le k\}\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.I` (`✓ std3`).

*Citation.* Markuss G. Ķēniņš; Arthemy V. Kiselev (2026). *Explicit class of finite-dimensional polynomial algebras with Wronskians over R^d as N-ary Lie brackets: beyond sl(2)*. URL: <https://arxiv.org/abs/2605.27305v2>.

*Commentary.*

I d k is the finite set of all finitely supported natural-valued multi-indices on Fin d whose total degree is at most k. Each index occurs once. These are the derivative indices in the source's complete Wronskian (TeX lines 613–630).

**Definition 1.2 (Iterated partial differentiation).**

$$\forall \left(K: \operatorname{Type}*\right), \left([\operatorname{Field}\left(K\right)], \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(\alpha: \operatorname{Finsupp}\left(\operatorname{Fin}\left(d\right), \mathbb{N}\right)\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.pderivMulti}\left(\left(K:= K\right), \left(d:= d\right), \alpha\right): \operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(K\right), \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(d\right), K\right), \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(d\right), K\right)\right)\right) = \operatorname{List.prod}\left(\operatorname{List.map}\left(\lambda \left(i: \operatorname{Fin}\left(d\right)\right) \mapsto \left(\operatorname{Derivation.toLinearMap}\left(\operatorname{MvPolynomial.pderiv}\left(i\right)\right)^{\alpha\left(i\right)}\right), \operatorname{List.finRange}\left(d\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.pderivMulti` (`✓ std3`).

*Citation.* Markuss G. Ķēniņš; Arthemy V. Kiselev (2026). *Explicit class of finite-dimensional polynomial algebras with Wronskians over R^d as N-ary Lie brackets: beyond sl(2)*. URL: <https://arxiv.org/abs/2605.27305v2>.

*Commentary.*

For a multi-index α, take the α i-th power of the linear map underlying the partial derivative in coordinate i, and multiply these endomorphisms along List.finRange d. Multiplication is composition, and the empty product is the identity. This is ordinary repeated partial differentiation, with no divided-power normalization (source, TeX lines 616–620). The definition applies over any field K.

**Definition 1.3 (The complete generalized Wronskian).**

$$\forall \left(K: \operatorname{Type}*\right), \left([\operatorname{Field}\left(K\right)], \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(k: \mathbb{N}\right), \left(\forall \left(f: \left(\{\left(\alpha: \operatorname{Finsupp}\left(\operatorname{Fin}\left(d\right), \mathbb{N}\right)\right) // \alpha \in \operatorname{D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.I}\left(d, k\right)\}\right) \to \left(\operatorname{MvPolynomial}\left(\operatorname{Fin}\left(d\right), K\right)\right)\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.wronskian}\left(\left(K:= K\right), \left(d:= d\right), \left(k:= k\right), f\right): \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(d\right), K\right)\right) = \operatorname{Matrix.det}\left(\lambda \left(\alpha: \{\left(\alpha: \operatorname{Finsupp}\left(\operatorname{Fin}\left(d\right), \mathbb{N}\right)\right) // \alpha \in \operatorname{D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.I}\left(d, k\right)\}\right) \mapsto \left(\lambda \left(\beta: \{\left(\alpha: \operatorname{Finsupp}\left(\operatorname{Fin}\left(d\right), \mathbb{N}\right)\right) // \alpha \in \operatorname{D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.I}\left(d, k\right)\}\right) \mapsto \left(\operatorname{DFunLike.coe}\left(\operatorname{D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.pderivMulti}\left(\left(K:= K\right), \left(d:= d\right), \operatorname{Subtype.val}\left(\alpha\right)\right)\right)\left(f\left(\beta\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.wronskian` (`✓ std3`).

*Citation.* Markuss G. Ķēniņš; Arthemy V. Kiselev (2026). *Explicit class of finite-dimensional polynomial algebras with Wronskians over R^d as N-ary Lie brackets: beyond sl(2)*. URL: <https://arxiv.org/abs/2605.27305v2>.

*Commentary.*

The rows are indexed by the differential multi-indices and the columns by the polynomial arguments f β. The entry in row α and column β is the α-th iterated partial derivative of f β. Its determinant is the complete generalized Wronskian of differential order k (source, TeX lines 625–630), expressed for polynomials over any field K. The index type is displayed as the subtype of multi-indices belonging to I d k; Subtype.val extracts a row's multi-index, and DFunLike.coe applies its linear map.

**Definition 1.4 (The one-generator polynomial extension).**

$$\forall \left(K: \operatorname{Type}*\right), \left([\operatorname{Field}\left(K\right)], \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(k: \mathbb{N}\right), \left(\forall \left(p: \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(d\right), K\right)\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.lonely}\left(\left(K:= K\right), \left(d:= d\right), \left(k:= k\right), p\right): \operatorname{Submodule}\left(K, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(d\right), K\right)\right)\right) = \operatorname{SemilatticeSup.sup}\left(\operatorname{MvPolynomial.restrictTotalDegree}\left(\operatorname{Fin}\left(d\right), K, k\right), \operatorname{Submodule.span}\left(K, \{p\}\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.lonely` (`✓ std3`).

*Citation.* Markuss G. Ķēniņš; Arthemy V. Kiselev (2026). *Explicit class of finite-dimensional polynomial algebras with Wronskians over R^d as N-ary Lie brackets: beyond sl(2)*. URL: <https://arxiv.org/abs/2605.27305v2>.

*Commentary.*

The subspace lonely p is the sum of the polynomials of total degree at most k and the line through p. The supremum is the sum of these submodules, and the line is the span of the singleton containing p. When p is nonzero and homogeneous of degree k + 1, this is the direct sum in the source's question (TeX lines 1258–1260). The definition itself requires neither homogeneity nor nonzeroness.

**Definition 1.5 (Perfectness of the extension).**

$$\forall \left(K: \operatorname{Type}*\right), \left([\operatorname{Field}\left(K\right)], \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(k: \mathbb{N}\right), \left(\forall \left(p: \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(d\right), K\right)\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.perfect}\left(\left(K:= K\right), \left(d:= d\right), \left(k:= k\right), p\right)\right) \Leftrightarrow \left(\operatorname{Submodule.span}\left(K, \{\left(w: \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(d\right), K\right)\right) \mid \exists \left(f: \left(\{\left(\alpha: \operatorname{Finsupp}\left(\operatorname{Fin}\left(d\right), \mathbb{N}\right)\right) // \alpha \in \operatorname{D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.I}\left(d, k\right)\}\right) \to \left(\operatorname{MvPolynomial}\left(\operatorname{Fin}\left(d\right), K\right)\right)\right), \left(\left(\forall \left(\beta: \{\left(\alpha: \operatorname{Finsupp}\left(\operatorname{Fin}\left(d\right), \mathbb{N}\right)\right) // \alpha \in \operatorname{D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.I}\left(d, k\right)\}\right), \left(f\left(\beta\right) \in \operatorname{D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.lonely}\left(\left(K:= K\right), \left(d:= d\right), \left(k:= k\right), p\right)\right)\right) \land \left(\operatorname{D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.wronskian}\left(\left(K:= K\right), \left(d:= d\right), \left(k:= k\right), f\right) = w\right)\right)\}\right) = \operatorname{D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.lonely}\left(\left(K:= K\right), \left(d:= d\right), \left(k:= k\right), p\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.perfect` (`✓ std3`).

*Citation.* Markuss G. Ķēniņš; Arthemy V. Kiselev (2026). *Explicit class of finite-dimensional polynomial algebras with Wronskians over R^d as N-ary Lie brackets: beyond sl(2)*. URL: <https://arxiv.org/abs/2605.27305v2>.

*Commentary.*

Perfectness means that the K-linear span of every Wronskian whose arguments lie in lonely p equals lonely p itself (source, TeX lines 517–521). This equality includes closure under the bracket as well as generation by bracket values. The definition does not require a nonzero or homogeneous p.

**Definition 1.6 (Existence exactly at differential order one).**

$$\left(\operatorname{D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.claim}\right) \Leftrightarrow \left(\forall \left(K: \operatorname{Type}\right), \left([\operatorname{Field}\left(K\right)], \left([\operatorname{CharZero}\left(K\right)], \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(k: \mathbb{N}\right), \left(\left(2 \le d\right) \to \left(\left(1 \le k\right) \to \left(\left(\exists \left(p: \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(d\right), K\right)\right), \left(\left(p \ne \left(0: \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(d\right), K\right)\right)\right) \land \left(\left(\operatorname{MvPolynomial.IsHomogeneous}\left(p, k + 1\right)\right) \land \left(\operatorname{D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.perfect}\left(\left(K:= K\right), \left(d:= d\right), \left(k:= k\right), p\right)\right)\right)\right)\right) \Leftrightarrow \left(k = 1\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Markuss G. Ķēniņš; Arthemy V. Kiselev (2026). *Explicit class of finite-dimensional polynomial algebras with Wronskians over R^d as N-ary Lie brackets: beyond sl(2)*. URL: <https://arxiv.org/abs/2605.27305v2>.

*Commentary.*

Over every characteristic-zero field K, for every d at least two and k at least one, there is a nonzero homogeneous polynomial p of degree k + 1 with a perfect extension if and only if k equals one. This answers the existence question of TeX lines 1258–1260 with a characterization of the possible orders, and includes both real and complex coefficients.

**Theorem 1.7 (The order obstruction and the quadratic construction).**

$$\forall \left(K: \operatorname{Type}\right), \left([\operatorname{Field}\left(K\right)], \left([\operatorname{CharZero}\left(K\right)], \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(k: \mathbb{N}\right), \left(\left(2 \le d\right) \to \left(\left(1 \le k\right) \to \left(\left(\exists \left(p: \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(d\right), K\right)\right), \left(\left(p \ne \left(0: \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(d\right), K\right)\right)\right) \land \left(\left(\operatorname{MvPolynomial.IsHomogeneous}\left(p, k + 1\right)\right) \land \left(\operatorname{D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.perfect}\left(\left(K:= K\right), \left(d:= d\right), \left(k:= k\right), p\right)\right)\right)\right)\right) \Leftrightarrow \left(k = 1\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.result` (`✓ std3`). ∎

*Resolves.* `Problems/kenins-kiselev-2026-wronskian-perfect-lonely-algebra` (proved) by `D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kenins-kiselev-2026-wronskian-perfect-lonely-algebra","declaration_gid":"D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Markuss G. Ķēniņš; Arthemy V. Kiselev (2026). *Explicit class of finite-dimensional polynomial algebras with Wronskians over R^d as N-ary Lie brackets: beyond sl(2)*. URL: <https://arxiv.org/abs/2605.27305v2>.

*Commentary.*

Start with the generating family consisting of p and the monomials x^α for α in I d k. Expand every argument of a Wronskian in this family. Multilinearity expresses every bracket as a linear combination of brackets of generators.

Iterated differentiation lowers integer-valued homogeneous degree by the order of differentiation. In each determinant term every row is used once, so for homogeneous arguments of degrees n β the bracket is homogeneous of degree the sum of n β minus the sum of the row degrees, with natural subtraction in the nonnegative formulation. This follows by first computing degrees with integer weights and then returning to natural degrees. If p is homogeneous of degree k + 1, a bracket containing every generator except p has degree zero, while omitting x^α gives degree k + 1 minus the degree of α.

A repeated generator gives two equal columns and determinant zero. An injective choice of generators omits exactly one member of the family and differs from the bracket that omits that member only by the sign of a column permutation. Thus the generator brackets all lie in the span of brackets obtained by omitting one generator. Suppose k is at least two. Project onto the homogeneous component of degree k. All these brackets vanish under this projection except the d brackets omitting a degree-one monomial. The projection of every bracket, and hence of their span, lies in a subspace s generated by these d polynomials. Perfectness would put the degree-k component of every element of lonely p in s. Choose the two distinct coordinates i₀ = 0 and i₁ = 1. The d pure powers x_i^k together with x_i₀^(k−1)x_i₁ are d + 1 distinct degree-k monomials. They belong to lonely p, are fixed by the projection, and are linearly independent. Thus d + 1 is at most the dimension of s, whereas its d generators give dimension at most d. This contradiction excludes perfectness for every homogeneous p when k is at least two.

For order one, the differential indices are zero and the single-coordinate unit multi-indices. Their operators are respectively the identity and the first partial derivatives. Reindex rows and columns by Option (Fin d), using none for zero and some i for the i-th unit index. The matrix on the monomials 1 and X i is the identity with its first row replaced by the vector consisting of 1 and X i, and its determinant is one.

For a homogeneous quadratic p, Euler's identity says that the sum of X i times the i-th partial derivative of p equals 2p. Consequently the column of p and its first partial derivatives is minus p times the constant column plus the sum of the i-th partial derivative of p times the X i column. Determinant multilinearity therefore evaluates a replacement in the constant column as minus p, and a replacement in the X i column as the i-th partial derivative of p. Each replacement stays in the original column position.

Take q to be the sum of (X i)^2 over Fin d. It is homogeneous of degree two, and its i-th partial derivative is (2 : K) times X i. Since there is a coordinate and the field has characteristic zero, this also proves q is nonzero. The brackets just evaluated all lie in lonely q: they are 1, minus q, and (2 : K) times X i. The generating-family expansion therefore puts every bracket in lonely q. Conversely, these brackets obtained by omitting one generator have arguments in lonely q. Their span contains 1 and q, and multiplication by the inverse of (2 : K) puts every X i in it. These polynomials generate lonely q, proving the reverse inclusion and hence perfectness.

Finally, existence together with k at least one forces k = 1, since every other such natural k is at least two and contradicts the obstruction. When k = 1, the polynomial q supplies nonzeroness, homogeneity and perfectness, proving the converse.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.I`
- Truth anchor: `D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.claim`
- Truth anchor: `D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.lonely`
- Truth anchor: `D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.pderivMulti`
- Truth anchor: `D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.perfect`
- Truth anchor: `D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.result`
- Truth anchor: `D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.wronskian`
- Dependency: [D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution](../Quantum/Algebra/WeightedPolynomialSubstitution.md)
