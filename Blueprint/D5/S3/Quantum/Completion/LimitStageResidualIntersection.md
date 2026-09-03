# Limit-Stage Residual Intersection

## Abstract

A limit-stage residual is the intersection of all predecessor residuals.

**Theorem 1.1 (Limit-stage residuals are predecessor intersections).**

$$\begin{aligned}\forall K, H, I: \operatorname{Type},\\{}[\operatorname{RCLike}\left(K\right)] \land [\operatorname{NormedAddCommGroup}\left(H\right)] \land [\operatorname{InnerProductSpace}\left(K, H\right)] \land\\{}[\operatorname{CompleteSpace}\left(H\right)] \land [\operatorname{Preorder}\left(I\right)],\\\forall V: I \to \operatorname{ClosedSubmodule}_{K}(H), lambda: I,\\V(lambda) = \operatorname{ClosedSup}\left(V(alpha)_{alpha<lambda}\right) \Rightarrow\\V(lambda)^{\perp} = \operatorname{Inf}\left(V(alpha)^{\perp}_{alpha<lambda}\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/LimitStageResidualIntersection.limit_stage_residual_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be an indexed family of closed subspaces in a complete real-or-complex inner-product space, and fix a stage lambda.

The premise identifies the space at lambda with the closed supremum of the spaces at all strictly earlier stages. This is the closed-subspace form of the closure of their union.

Orthogonal complementation sends that closed supremum to the intersection of the orthogonal residuals at every predecessor. The proof directly applies the pinned Mathlib identity ClosedSubmodule.iInf_orthogonal.

## References

- Truth anchor: `D5/S3/Quantum/Completion/LimitStageResidualIntersection.limit_stage_residual_intersection`
