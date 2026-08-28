# Longitudinal Structural Causal Model

## Abstract

Finite longitudinal policies preserve state mechanisms and expose feedback effects.

**Definition 1.1 (Dynamic policy).**

Lean statement: `D5/S3/ConceptDynamics/LongitudinalCausal/LongitudinalStructuralCausalModel.dynamicPolicy`

*Formalization.* `D5/S3/ConceptDynamics/LongitudinalCausal/LongitudinalStructuralCausalModel.dynamicPolicy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At each finite time, a dynamic policy maps the exact observed history to a probability mass function on actions.

**Definition 1.2 (Policy intervention).**

Lean statement: `D5/S3/ConceptDynamics/LongitudinalCausal/LongitudinalStructuralCausalModel.policyIntervention`

*Formalization.* `D5/S3/ConceptDynamics/LongitudinalCausal/LongitudinalStructuralCausalModel.policyIntervention` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A policy intervention replaces the behavior assignment while preserving the initial law, state-transition mechanism, and outcome map.

**Definition 1.3 (Policy result).**

Lean statement: `D5/S3/ConceptDynamics/LongitudinalCausal/LongitudinalStructuralCausalModel.policyResult`

*Formalization.* `D5/S3/ConceptDynamics/LongitudinalCausal/LongitudinalStructuralCausalModel.policyResult` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The policy result is the final outcome law after sequentially sampling every policy action and retained state transition.

**Theorem 1.4 (Static intervention is the length-one case).**

$$policyResult\left(model, staticPolicyEmbedding\left(x\right)\right) = staticInterventionResult\left(model, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/LongitudinalCausal/LongitudinalStructuralCausalModel.static_intervention_is_length_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant policy embedding and the direct static intervention induce the same probability mass function on final outcomes.

**Theorem 1.5 (Feedback changes a two-step result law).**

$$policyResult\left(feedbackModel, feedbackPolicy\right) \ne feedbackIgnoringStaticResult$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/LongitudinalCausal/LongitudinalStructuralCausalModel.feedback_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the Boolean witness, the first action becomes the next covariate and the second action reads it. The dynamic law is therefore distinct from the feedback-ignoring static result.

**Theorem 1.6 (Removing feedback restores agreement).**

$$policyResult\left(noFeedbackModel, feedbackPolicy\right) = policyResult\left(noFeedbackModel, feedbackIgnoringPolicy\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/LongitudinalCausal/LongitudinalStructuralCausalModel.no_feedback_static_dynamic_agree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the matched two-step model with the action-to-state link removed, the dynamic and feedback-ignoring policy laws coincide.

## References

- Truth anchor: `D5/S3/ConceptDynamics/LongitudinalCausal/LongitudinalStructuralCausalModel.dynamicPolicy`
- Truth anchor: `D5/S3/ConceptDynamics/LongitudinalCausal/LongitudinalStructuralCausalModel.feedback_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/LongitudinalCausal/LongitudinalStructuralCausalModel.no_feedback_static_dynamic_agree`
- Truth anchor: `D5/S3/ConceptDynamics/LongitudinalCausal/LongitudinalStructuralCausalModel.policyIntervention`
- Truth anchor: `D5/S3/ConceptDynamics/LongitudinalCausal/LongitudinalStructuralCausalModel.policyResult`
- Truth anchor: `D5/S3/ConceptDynamics/LongitudinalCausal/LongitudinalStructuralCausalModel.static_intervention_is_length_one`
