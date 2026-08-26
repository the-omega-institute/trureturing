# Visible Autonomy Criterion

## Abstract

Visible-state descent, kernel stability, and zero hidden-to-visible flow are equivalent for every idempotent linear projection.

**Theorem 1.1 (Visible autonomy through an idempotent projection).**

$$\begin{aligned}\forall R, X: \operatorname{Type},\\\operatorname{Semiring}(R) \land \operatorname{AddCommGroup}(X) \land \operatorname{Module}(R, X) \Rightarrow\\\forall P, T: \operatorname{LinearMap}(R, X, X),\\P \circ P = P \Rightarrow\\\operatorname{let} Q : = 1 - P,\\V : = \operatorname{range}(P),\\visible : = \operatorname{rangeRestrict}(P),\\visibleAfter : = \operatorname{codRestrict}(V, P \circ T) \operatorname{in}\\\operatorname{ListTFAE}({[\exists descended: \operatorname{LinearMap}(R, V, V), visibleAfter = descended \circ visible, \operatorname{ker}(P) \subseteq \operatorname{ker}(P \circ T), P \circ T \circ Q = 0]}) \land\\(visibleCoordinateProjection \circ visibleCoordinateProjection = visibleCoordinateProjection \land hiddenCoordinateProjection = 1 - visibleCoordinateProjection \land\\visibleCoordinateProjection \circ visibleToHiddenLeak \circ hiddenCoordinateProjection = 0 \land hiddenCoordinateProjection \circ visibleToHiddenLeak \circ visibleCoordinateProjection \neq 0).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/VisibleDescent/VisibleAutonomyCriterion.visible_autonomy_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The visible state is constructed canonically by restricting an idempotent linear projection to its range. The next visible state is the range-valued restriction of projection after the ambient dynamics.

A descended range endomorphism exists exactly when the projection kernel is stable under the next-visible map, equivalently when the complementary hidden component has zero flow into the next visible state.

The imported two-coordinate rational example uses the same visible projection, hidden complement, and update in both cross blocks. Its hidden-to-visible block vanishes while the reverse block does not, so the criterion is strictly one-sided.

## References

- Truth anchor: `D5/S3/Observer/VisibleDescent/VisibleAutonomyCriterion.visible_autonomy_criterion`
- Dependency: [D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria](../HiddenFlow/VisibleHiddenProjectionCriteria.md)
