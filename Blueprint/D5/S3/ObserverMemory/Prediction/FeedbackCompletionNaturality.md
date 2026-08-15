# Feedback Completion Naturality

## Abstract

Projected-state feedback preserves a family of semiconjugate updates.

**Theorem 1.1 (Projected-state feedback preserves semiconjugate updates).**

$$\forall Y, Z, U: \operatorname{Type},\ update: U \to \left(Y \to Y\right),\ completedUpdate: U \to \left(Z \to Z\right),\ projection: Y \to Z, feedback: Z \to U,\ (\forall u, projection \circ update(u) = completedUpdate(u) \circ projection) \Rightarrow projection \circ (y \mapsto update(feedback(projection(y)))(y)) = (z \mapsto completedUpdate(feedback(z))(z)) \circ projection.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FeedbackCompletionNaturality.feedback_completion_naturality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let update and completedUpdate be families of state updates indexed by a common control type, and let projection map the original state into the completed state. Assume projection semiconjugates the two updates for every control value.

Choose each control value by applying feedback to the projected current state. Then projection also semiconjugates the resulting closed-loop updates. The control on both sides is identical because it depends only on that projected state.

Loogle found Function.Semiconj.comp_eq as an exact library result for turning pointwise semiconjugacy into function equality; the Lean proof imports and applies it. Loogle also returned the pointwise and equivalence forms, while a shaped family query did not elaborate. LeanSearch returned only generic semiconjugacy and flow results. Repository and receipt searches found no equal or stronger closed-loop theorem. A Boolean instance witnesses that the hypotheses are satisfiable.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/FeedbackCompletionNaturality.feedback_completion_naturality`
