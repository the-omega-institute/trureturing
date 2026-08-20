# Prediction Completion Idempotence

## Abstract

Predictive completion separates completed states and is idempotent.

**Theorem 1.1 (Prediction completion is idempotent).**

$$\forall Y, O: \operatorname{Type},\ \forall tau: Y \to Y, q: Y \to O,\ (\forall z, zPrime \in Z_{q},\ \widehat{R_{q}}(z, zPrime) \iff z = zPrime) \land\ \operatorname{Quotient}(\widehat{R_{q}}) \equiv Z_{q}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Refinement/PredictionCompletionIdempotence.prediction_completion_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary state update and readout, the completed state space is the quotient by equality of complete future readout itineraries. Its update and current readout descend from those source maps.

On that completed system, the second-stage relation again compares every future readout. The representative calculation supplied by the cascade theorem and quotient induction show that this relation is exactly equality on all completed states.

Specializing the exact repository cascade-completion theorem to the same readout on both stages and the identity forgetful map supplies the displayed equivalence from the second quotient back to the first completed state space.

Repository search found the exact cascade_completion and second_stage_relation_projection declarations. Pinned Mathlib supplies Quotient.inductionOn₂' and Quotient.eq; all four hits are applied directly in the Lean theorem.

## References

- Truth anchor: `D5/S3/ObserverMemory/Refinement/PredictionCompletionIdempotence.prediction_completion_idempotent`
- Dependency: [D5/S3/ObserverMemory/Refinement/CascadeCompletion](CascadeCompletion.md)
