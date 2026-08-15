# Quotient and Orthogonal Complement

## Abstract

The canonical quotient isometrically identifies the orthogonal complement.

**Theorem 1.1 (The canonical quotient map is an isometric equivalence).**

$$\forall k, E: \operatorname{Type},\ [\operatorname{RCLike}(k)],\ [\operatorname{NormedAddCommGroup}(E)],\ [\operatorname{InnerProductSpace}_{k}(E)],\ K: \operatorname{Submodule}_{k}(E),\ [\operatorname{HasOrthogonalProjection}(K)],\ \operatorname{Isometry}(\operatorname{quotientEquivOrthogonal}\left(K\right)) \land \operatorname{Bijective}(\operatorname{quotientEquivOrthogonal}\left(K\right)) \land (\forall x: E,\ \operatorname{quotientEquivOrthogonal}\left(K\right)([x]) = x - \operatorname{starProjection}\left(K, x\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/QuotientOrthogonalComplement.quotient_orthogonal_complement_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be a real-or-complex scalar field, E an inner-product space over k, and K a subspace admitting an orthogonal projection. The exact Mathlib map quotientEquivOrthogonal carries linearity in its type. The first two conjuncts state that its underlying function is an isometry and a bijection, hence a linear isometric equivalence from E modulo K onto the orthogonal complement of K.

For every x in E, the last conjunct identifies the underlying vector of the image of the quotient class of x with x minus its canonical orthogonal projection onto K. Thus the formal statement includes both the source formula for the canonical map and the assertion that this map is an isometric equivalence.

Loogle found Submodule.quotientEquivOrthogonal exactly. LeanSearch returned related quotient-complement equivalences but not that exact declaration among its first ten results. The pinned Mathlib tree contains the exact construction, which is imported and reused; its coercion theorem and the complementary-projection identity prove the displayed formula without reconstructing the equivalence.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/QuotientOrthogonalComplement.quotient_orthogonal_complement_isometry`
