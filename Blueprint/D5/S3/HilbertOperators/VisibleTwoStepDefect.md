# Visible two-step compression defect

## Abstract

The defect between two full steps and two successively projected steps detects when a symmetric time operator leaves the visible subspace invariant.

**Definition 1.1 (The quadratic defect on a visible vector).**

$$d(v)=\langle v,(PT^2-PTPT)v\rangle$$

*Formalization.* `D5/S3/HilbertOperators/VisibleTwoStepDefect.defectForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let V be a subspace of a real inner-product space that admits the orthogonal projection P. On v in V, compare the final projections after two bounded linear steps T, with and without a projection between the steps.

**Theorem 1.2 (Squared leakage and invariance).**

$$\begin{aligned}&\forall v\in V, d(v)=\Vert(1-P)Tv\Vert^2\\&(\forall v\in V, d(v)=0) \Leftrightarrow (\forall v\in V, Tv\in V)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/VisibleTwoStepDefect.visible_two_step_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose T is symmetric. Move the outer projection across the inner product, where it fixes v, and then move one copy of T. Orthogonality removes the projection of Tv against its residual. The remaining inner product is the squared residual norm, which vanishes exactly when Tv belongs to V.

## References

- Truth anchor: `D5/S3/HilbertOperators/VisibleTwoStepDefect.defectForm`
- Truth anchor: `D5/S3/HilbertOperators/VisibleTwoStepDefect.visible_two_step_defect`
