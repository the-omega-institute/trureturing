# Consumption and Production Input Separation

## Abstract

A finite two-artifact model separates runtime consumption from production input.

**Theorem 1.1 (Consumption is not inverse to production input).**

$$\begin{gathered}\exists x, y: Bool,\\{}consumers: Bool \to \operatorname{Set}\left(Bool\right), prodInputs: Bool \to \operatorname{Option}\left(\operatorname{Set}\left(Bool\right)\right),\\{}x \neq y \land consumers(x) = \{y\} \land\\{}y \in consumers(x) \land prodInputs(y) = \operatorname{some}\left(\emptyset\right) \land\\{}\neg (x \in \emptyset).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Governance/ConsumptionProductionInputSeparation.consumption_not_inverse_to_production_input` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take Bool as the two-element artifact type, with x=false and y=true. The runtime-consumer set at x is the singleton containing y.

The partial production-input map is defined at y with the empty set. Thus y consumes x at runtime while x is absent from the inputs used to produce y.

The witness keeps the two relations distinct: runtime reads need not be inverse images of production-input records.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Governance/ConsumptionProductionInputSeparation.consumption_not_inverse_to_production_input`
