# Isometries fixing a subspace pointwise

## Abstract

For a subspace K of an inner product space E over the real or complex numbers that admits an orthogonal projection, restriction to the orthogonal complement is a group isomorphism from the linear isometries of E fixing K pointwise onto the linear isometries of the orthogonal complement; when E is finite-dimensional it preserves the determinant.

Throughout, k is a field of real or complex scalars (an RCLike field), E is an inner product space over k, K is a subspace of E, and K^perp denotes the orthogonal complement of K. The linear isometries of E onto itself form a group under composition, written LinearIsometryEquiv(E, E).

**Definition 1.1 (The pointwise stabilizer of a subspace).**

$$\forall k: \operatorname{Type}, [\operatorname{RCLike}\left(k\right)], \forall E: \operatorname{Type}, [\operatorname{NormedAddCommGroup}\left(E\right)], [\operatorname{InnerProductSpace}\left(k, E\right)], \forall K: \operatorname{Submodule}\left(k, E\right), \forall U \in \operatorname{LinearIsometryEquiv}\left(E, E\right),\; U \in \operatorname{pointwiseStabilizer}\left(K\right) \Leftrightarrow \left(\forall x \in K,\; U\left(x\right) = x\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/Unitary/PointwiseStabilizer.pointwiseStabilizer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

pointwiseStabilizer(K) is the subgroup of the linear isometries U of E onto itself with U(x) = x for every vector x of K. It contains the identity, and it is closed under composition and inverses: if U and V fix every vector of K, so does U V, and U(x) = x gives U^-1(x) = x.

**Theorem 1.2 (Restriction to the orthogonal complement).**

$$\forall k: \operatorname{Type}, [\operatorname{RCLike}\left(k\right)], \forall E: \operatorname{Type}, [\operatorname{NormedAddCommGroup}\left(E\right)], [\operatorname{InnerProductSpace}\left(k, E\right)], \forall K: \operatorname{Submodule}\left(k, E\right), [\operatorname{HasOrthogonalProjection}\left(K\right)], \exists e \in \operatorname{MulEquiv}\left(\operatorname{pointwiseStabilizer}\left(K\right), \operatorname{LinearIsometryEquiv}\left(K^{\perp}, K^{\perp}\right)\right),\; \left(\forall U \in \operatorname{pointwiseStabilizer}\left(K\right),\; \forall y \in K^{\perp},\; e\left(U\right)\left(y\right) = U\left(y\right)\right) \land \left(\operatorname{FiniteDimensional}\left(k, E\right) \Rightarrow \left(\forall U \in \operatorname{pointwiseStabilizer}\left(K\right),\; \operatorname{det}\left(U\right) = \operatorname{det}\left(e\left(U\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Unitary/PointwiseStabilizer.exists_mulEquiv_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the display, MulEquiv(A, B) is the type of group isomorphisms from A onto B, e(U) is the isometry of K^perp assigned to U, the equation e(U)(y) = U(y) compares the two sides as vectors of E, det(U) is the determinant of U as a linear map of E, and det(e(U)) is the determinant of e(U) as a linear map of K^perp. The theorem assumes that K has an orthogonal projection, that is, every vector of E is the sum of a vector of K and a vector of K^perp; this holds for instance when K is complete, in particular when K is finite-dimensional. It states that there is a group isomorphism e from pointwiseStabilizer(K) onto the linear isometries of K^perp which is restriction, e(U)(y) = U(y) for every U and every y in K^perp, and that if E is finite-dimensional then det(U) = det(e(U)) for every U.

An isometry U fixing K pointwise preserves inner products and maps K onto itself, so its inverse also fixes K and U maps K^perp onto K^perp. Restriction to K^perp is therefore a homomorphism of groups; this step uses no hypothesis on K. Injectivity and surjectivity use the decomposition of every vector as k + y with k in K and y in K^perp: two elements with the same restriction agree on both summands, and an isometry W of K^perp is the restriction of the isometry that is the identity on K and W on K^perp, assembled through the orthogonal decomposition of E as the orthogonal sum of K and K^perp. For the determinant, U(x) - x lies in K^perp for every x, because U(k + y) - (k + y) = U(y) - y. Hence U leaves K^perp invariant and induces the identity on the quotient E / K^perp, and the determinant of a map preserving a subspace is the product of the determinants on the subspace and on the quotient; this gives det(U) = det(e(U)) times 1. The finite dimension is required of E and not only of K^perp. The determinant of a linear map of a space that has no finite basis is 1 by convention, so for an infinite-dimensional E and a closed K whose complement K^perp is a line, the isometry that is the identity on K and -1 on K^perp has determinant 1 on E and -1 on K^perp; this example is a remark and is not formalised. The hypothesis that K has an orthogonal projection is equivalent to the statement that K and K^perp together span E, which the surjectivity step uses; this equivalence is a remark and is not formalised. The result is an elementary fact of linear algebra; it is stated here for every RCLike field and for spaces of any dimension.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/PointwiseStabilizer.exists_mulEquiv_orthogonal`
- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/PointwiseStabilizer.pointwiseStabilizer`
