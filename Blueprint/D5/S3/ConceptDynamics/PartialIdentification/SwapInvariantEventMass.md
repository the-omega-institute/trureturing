# Swap-Invariant Event Masses

## Abstract

Swap-connected causal orders induce identical event masses, finite event profiles, and linear query values under every fixed exogenous law.

Pointwise equality of structural response profiles is transported through a finite exogenous weighted sum. Probability normalization is irrelevant to this pure invariance identity.

The result applies simultaneously to a finite family of Boolean final-state events and to every rational linear objective assembled from their masses.

This is the semantic-to-linear bridge needed to prove that causal-order LP data and query values do not depend on the selected compatible extension once swap connectivity is available.

**Theorem 1.1 (Swap-connected orders assign equal mass to every event).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/SwapInvariantEventMass.eventMass_invariant_of_swap_chain`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/SwapInvariantEventMass.eventMass_invariant_of_swap_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every summand agrees because the event readout agrees pointwise for the same exogenous state.

**Theorem 1.2 (The complete finite event profile is extension invariant).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/SwapInvariantEventMass.eventMassProfile_invariant_of_swap_chain`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/SwapInvariantEventMass.eventMassProfile_invariant_of_swap_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality applies the scalar event-mass identity to every compiled event index.

**Theorem 1.3 (Every linear query on the event profile is invariant).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/SwapInvariantEventMass.linearEventQuery_invariant_of_swap_chain`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/SwapInvariantEventMass.linearEventQuery_invariant_of_swap_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of event-mass profiles immediately preserves all rational linear objectives used by the finite causal LP layer.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/SwapInvariantEventMass.eventMassProfile_invariant_of_swap_chain`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/SwapInvariantEventMass.eventMass_invariant_of_swap_chain`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/SwapInvariantEventMass.linearEventQuery_invariant_of_swap_chain`
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/SwapClosureExtensionInvariance](SwapClosureExtensionInvariance.md)
