# External Prediction and Reflective Autonomy

## Abstract

Refinement constructs an external action predictor, and such predictability coexists with reflective autonomy.

**Theorem 1.1 (External prediction is compatible with reflective autonomy).**

$$\left(\forall X \in \operatorname{Type}, Reason \in \operatorname{Type}, External \in \operatorname{Type}, U \in \operatorname{Type}, R \in X \to Reason, E \in X \to External, pi \in Reason \to U,\; \operatorname{Refines}\left(R, E\right) \Rightarrow \left(\exists p \in External \to Reason,\; R = p \circ E \land pi \circ R = pi \circ p \circ E\right)\right) \land \left(\exists R \in Bool \to Bool, E \in Bool \to Bool, p \in Bool \to Bool, pi \in Bool \to Bool, A \in Bool \to Bool, Available \in Bool \to \operatorname{Set}\left(Bool\right), V \in Bool \to \left(Bool \to Prop\right), rho \in Bool \to Bool, x \in Bool,\; R = p \circ E \land \left(A = pi \circ R \land \left(A = pi \circ p \circ E \land \left(A\left(x\right) \in Available\left(x\right) \land \left(V\left(x, A\left(x\right)\right) \land \left(A\left(rho\left(x\right)\right) = A\left(x\right) \land V\left(rho\left(x\right), A\left(x\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Agency/ExternalPredictionReflectiveAutonomy.external_prediction_compatible_with_reflective_autonomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the reason readout R factors through an external readout E by p, the action policy pi factors through E by the constructed predictor pi composed with p.

The second public clause is a shared Boolean model. Its same reason, external readout, factor, policy, and action witness both internal control and external prediction.

That model also makes the selected action available, approved before reflection, unchanged by reflection, and approved afterwards. Thus predictability alone does not negate reflective autonomy.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Agency/ExternalPredictionReflectiveAutonomy.external_prediction_compatible_with_reflective_autonomy`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
