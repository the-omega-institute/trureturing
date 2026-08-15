# Finite-Layer Projection Escape

## Abstract

A nonzero orthogonal residual contains a unit vector at distance one.

**Theorem 1.1 (A nonzero orthogonal residual has a unit escape vector).**

$$\forall k, V: \operatorname{Type},\ [\operatorname{RCLike}(k)],\ [\operatorname{NormedAddCommGroup}(V)],\ [\operatorname{InnerProductSpace}_{k}(V)],\ [\operatorname{CompleteSpace}(V)],\ S: \operatorname{ClosedSubmodule}_{k}(V),\ S^{\perp} \neq \{0\} \Rightarrow \exists e: V,\ e \in S^{\perp} \land \operatorname{norm}\left(e\right) = 1 \land P_{S}(e) = 0 \land \operatorname{infDist}(e,S) = 1 \land \operatorname{norm}\left(I - P_{S}\right) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/FiniteLayerProjectionEscape.finite_layer_projection_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a closed subspace of a complete real or complex inner-product space. If its orthogonal complement is nonzero, there is a unit vector e in that complement. The projection onto S annihilates e, and the distance from e to S is exactly one.

The same hypothesis makes the projection onto the orthogonal complement nonzero. That projection equals the identity minus the projection onto S and has operator norm one.

The proof reuses the repository's complementary-projection identity. Pinned Mathlib supplies the nonzero subspace witness, the minimal-distance characterization of orthogonal projection, and the exact norm of a nonzero orthogonal projection. Natural-language name searches found no single declaration bundling all conclusions.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/FiniteLayerProjectionEscape.finite_layer_projection_escape`
- Dependency: [D5/S3/Quantum/Algebra/OrthogonalProjectionComplement](OrthogonalProjectionComplement.md)
