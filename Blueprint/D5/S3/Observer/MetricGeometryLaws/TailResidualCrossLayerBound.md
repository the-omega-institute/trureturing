# Tail Residual Cross-Layer Bound

## Abstract

A Lipschitz update separates a coarse defect into a fine tail and cross-layer defect.

**Theorem 1.1 (Tail residual cross-layer defect bound).**

$$V_{m} \subseteq V_{n} \land \operatorname{Lipschitz}_{L}(F) \Rightarrow \left\lVert P_{m}(F(X)) - P_{m}(F(P_{m}(X))) \right\rVert \leq L \left\lVert X - P_{n}(X) \right\rVert + \left\lVert P_{m}(F(P_{n}(X))) - P_{m}(F(P_{m}(P_{n}(X)))) \right\rVert.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/TailResidualCrossLayerBound.tail_residual_cross_layer_defect_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V_m be a visible Hilbert subspace of V_n, with canonical orthogonal projections P_m and P_n. Let F be L-Lipschitz.

The coarse defect compares projecting F(X) with projecting F after the coarse projection. It is bounded by the Lipschitz image of the unresolved V_n tail plus the same defect evaluated after the fine projection.

Both defect terms are expanded directly from F and the canonical projections. The proof inserts the fine projected update, applies the triangle inequality and projection contraction, then uses P_m P_n = P_m for nested subspaces.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/TailResidualCrossLayerBound.tail_residual_cross_layer_defect_bound`
- Dependency: [D5/S3/Observer/MetricGeometry/DefectDecomposition](../MetricGeometry/DefectDecomposition.md)
- Dependency: [D5/S3/Quantum/Algebra/OrthogonalProjectionComplement](../../Quantum/Algebra/OrthogonalProjectionComplement.md)
