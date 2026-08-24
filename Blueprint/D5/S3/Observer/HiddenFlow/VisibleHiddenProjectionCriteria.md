# Visible-Hidden Projection Criteria

## Abstract

Complementary projections characterize invariant, coinvariant, and reducing subspaces, with a concrete asymmetric leakage witness.

**Lemma 1.1 (The hidden projection is identity minus the visible projection).**

$$\operatorname{hiddenProjection}\left(V, R, h\right) = I - \operatorname{visibleProjection}\left(V, R, h\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria.hiddenProjection_eq_one_sub_visibleProjection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For complementary subspaces V and R with a chosen complement witness, the projection onto R along V is the identity operator minus the projection onto V along R.

This complement identity supplies the algebraic relation between the two projections used in the invariant and reducing criteria below.

**Lemma 1.2 (Visible invariance is equivalent to a zero hidden-visible block).**

$$\operatorname{IsInvariant}\left(T, V\right) \iff \operatorname{hiddenProjection}\left(V, R, h\right) \circ T \circ \operatorname{visibleProjection}\left(V, R, h\right) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria.visible_invariant_iff_hidden_visible_block_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an endomorphism T and a complementary decomposition into visible V and hidden R, V is invariant exactly when the hidden projection after T after the visible projection is the zero map.

The block vanishes because T sends every vector of V back into V; conversely, a zero hidden component forces that invariance.

**Lemma 1.3 (Hidden invariance is equivalent to a zero visible-hidden block).**

$$\operatorname{IsInvariant}\left(T, R\right) \iff \operatorname{visibleProjection}\left(V, R, h\right) \circ T \circ \operatorname{hiddenProjection}\left(V, R, h\right) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria.hidden_invariant_iff_visible_hidden_block_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same complementary decomposition, the hidden subspace R is invariant under T exactly when the visible projection after T after the hidden projection is the zero map.

Thus the visible component detects precisely the failure of T to keep vectors from R inside R.

**Theorem 1.4 (A reducing decomposition is exactly two vanishing cross blocks).**

$$\operatorname{IsReducing}\left(T, V, R\right) \iff (\operatorname{visibleProjection}\left(V, R, h\right) \circ T \circ \operatorname{hiddenProjection}\left(V, R, h\right) = 0 \land \operatorname{hiddenProjection}\left(V, R, h\right) \circ T \circ \operatorname{visibleProjection}\left(V, R, h\right) = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria.reducing_iff_cross_projection_blocks_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complementary decomposition reduces T when both V and R are invariant under T. Equivalently, both cross-component maps vanish: the visible-after-T-after-hidden block and the hidden-after-T-after-visible block are zero.

The criterion packages the two one-sided invariance equivalences into a single characterization of complete absence of visible-hidden leakage.

**Lemma 1.5 (A vanishing visible-hidden direction can coexist with hidden leakage).**

$$\operatorname{visibleCoordinateProjection}\left(\right) \circ \operatorname{visibleToHiddenLeak}\left(\right) \circ \operatorname{hiddenCoordinateProjection}\left(\right) = 0 \land \operatorname{hiddenCoordinateProjection}\left(\right) \circ \operatorname{visibleToHiddenLeak}\left(\right) \circ \operatorname{visibleCoordinateProjection}\left(\right) \neq 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria.visible_descent_does_not_prevent_hidden_leakage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the two-coordinate rational space, the visible and hidden coordinate projections select the first and second axes. The square-zero update sends the visible first coordinate into the hidden second one.

The visible-after-update-after-hidden composition is zero, while the opposite hidden-after-update-after-visible composition is nonzero. Therefore a one-sided visible descent test does not exclude hidden leakage.

## References

- Truth anchor: `D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria.hiddenProjection_eq_one_sub_visibleProjection`
- Truth anchor: `D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria.hidden_invariant_iff_visible_hidden_block_eq_zero`
- Truth anchor: `D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria.reducing_iff_cross_projection_blocks_eq_zero`
- Truth anchor: `D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria.visible_descent_does_not_prevent_hidden_leakage`
- Truth anchor: `D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria.visible_invariant_iff_hidden_visible_block_eq_zero`
