# Off-Policy Residual Identifiability

## Abstract

Behavior laws identify a target policy exactly when no model pair remains ambiguous.

**Theorem 1.1 (An empty off-policy residual characterizes identifiability).**

$$\operatorname{IdentifiableFromBehaviorLaw}\left(behaviorLaw, targetPolicyLaw\right) \Leftrightarrow \operatorname{offPolicyResidual}\left(behaviorLaw, targetPolicyLaw\right) = EmptySet$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/OffPolicyResidualIdentifiability.target_policy_identifiable_iff_off_policy_residual_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A behavior law and a target-policy law are readouts on the same model class. Identifiability means that any two models with the same behavior law have the same target-policy law.

The off-policy residual consists exactly of model pairs with equal behavior laws and unequal target-policy laws. Fiber constancy is therefore equivalent to emptiness of this residual, including for an empty model class.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/OffPolicyResidualIdentifiability.target_policy_identifiable_iff_off_policy_residual_empty`
- Dependency: [D5/S3/ConceptDynamics/Experiment/ExperimentValueIsKernelReduction](ExperimentValueIsKernelReduction.md)
