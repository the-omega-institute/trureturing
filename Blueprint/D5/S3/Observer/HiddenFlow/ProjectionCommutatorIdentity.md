# Projection Commutator Identity

## Abstract

A complementary split expresses a commutator through its two directed cross blocks, and projection commutation is exactly their joint vanishing.

**Theorem 1.1 (The commutator is the difference of the directed cross blocks).**

$$\forall A, [\operatorname{Ring}\left(A\right)], \forall P, Q, T \in A, Q = 1 - P \Rightarrow P \cdot T - T \cdot P = P \cdot T \cdot Q - Q \cdot T \cdot P.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity.commutator_eq_cross_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In any possibly noncommutative ring, let Q be the complement 1 minus P. Then P times T minus T times P equals the P-to-Q cross term minus the Q-to-P cross term.

Inserting P plus Q as the identity on both sides separates the two diagonal PTP terms, which cancel. No idempotence or nondegeneracy condition on P is required, so the identity also includes the degenerate complements P = 0 and P = 1 and the zero ring.

**Lemma 1.2 (Visible projection commutes exactly when both cross blocks vanish).**

$$\forall V, R, h: \operatorname{IsCompl}\left(V, R\right), T, \operatorname{visibleProjectionMatrix}\left(V, R, h\right) \cdot T = T \cdot \operatorname{visibleProjectionMatrix}\left(V, R, h\right) \iff (\operatorname{visibleProjection}\left(V, R, h\right) \circ \operatorname{matrixToLinear}\left(T\right) \circ \operatorname{hiddenProjection}\left(V, R, h\right) = 0 \land \operatorname{hiddenProjection}\left(V, R, h\right) \circ \operatorname{matrixToLinear}\left(T\right) \circ \operatorname{visibleProjection}\left(V, R, h\right) = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity.visible_projection_commutes_iff_cross_blocks_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For complementary subspaces V and R of a finite complex coordinate space, the matrix of the projection onto V along R commutes with T exactly when both directed cross-component maps are zero.

The visible-after-T-after-hidden block measures flow from R into V, while the hidden-after-T-after-visible block measures flow from V into R. Their simultaneous vanishing is the reducing condition, so it is equivalent to projection commutation.

## References

- Truth anchor: `D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity.commutator_eq_cross_blocks`
- Truth anchor: `D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity.visible_projection_commutes_iff_cross_blocks_eq_zero`
- Dependency: [D5/S3/Observer/HiddenFlow/InfinitesimalReducingCriterion](InfinitesimalReducingCriterion.md)
