# Safe Actions Under Readout Refinement

## Abstract

A finer readout enlarges the action set safe throughout the current fiber.

**Theorem 1.1 (Refinement enlarges the fiber-safe action set).**

$$\forall X \in \operatorname{Type}, Q \in \operatorname{Type}, R \in \operatorname{Type}, A \in \operatorname{Type}, q \in X \to Q, r \in X \to R, Legal \in X \to \left(A \to Prop\right), f \in R \to Q, x \in X,\; q = f \circ r \Rightarrow \left\{\forall y \in X,\; q\left(y\right) = q\left(x\right) \Rightarrow Legal\left(y\right)\left(a\right) \mid a \in A\right\} \subseteq \left\{\forall y \in X,\; r\left(y\right) = r\left(x\right) \Rightarrow Legal\left(y\right)\left(a\right) \mid a \in A\right\}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/SafeActionRefinementMonotonicity.safe_action_refinement_monotonicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state-wise legality predicate is a source primitive. For a readout and current state, the displayed action set contains exactly those actions legal at every state in the same readout fiber.

The factorization q = f composed with r makes the current r-fiber a subset of the current q-fiber. Intersecting the same legal-action family over the smaller fiber can only enlarge the result.

The Lean proof applies Mathlib's bounded-intersection antitonicity theorem to the fiber inclusion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Decision/SafeActionRefinementMonotonicity.safe_action_refinement_monotonicity`
