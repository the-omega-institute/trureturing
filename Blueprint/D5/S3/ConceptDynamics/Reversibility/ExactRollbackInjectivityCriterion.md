# Exact Rollback and Joint-Record Injectivity

## Abstract

Exact rollback from a joint update-log record is equivalent to injectivity.

**Theorem 1.1 (Exact rollback criterion).**

$$\begin{gathered}\forall X, Y, M: \operatorname{Type},\\{}\operatorname{Nonempty}\left(X\right) \Rightarrow\\{}\forall U: X \to Y, L: X \to M,\\{}(\exists R: Y \times M \to X, \forall x: X, R(\operatorname{conceptJoin}\left(U, L\right)(x)) = x) \iff \operatorname{Injective}\left(\operatorname{conceptJoin}\left(U, L\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Reversibility/ExactRollbackInjectivityCriterion.exact_rollback_iff_joint_record_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint record is the canonical product readout of the update and log channels. An exact rollback map is precisely a left inverse of this readout.

Pinned Mathlib equates existence of a left inverse with injectivity. Applying that equivalence gives both directions of the criterion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Reversibility/ExactRollbackInjectivityCriterion.exact_rollback_iff_joint_record_injective`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
