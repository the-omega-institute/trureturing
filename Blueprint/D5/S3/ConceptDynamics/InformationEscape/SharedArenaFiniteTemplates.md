# SharedArenaFiniteTemplates

## Abstract

Homogeneous finite-output readouts retain two causal slots for shared-arena registrations.

**Definition 1.1 (Finite Boolean-indexed signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/SharedArenaFiniteTemplates.finiteSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/SharedArenaFiniteTemplates.finiteSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Boolean-indexed signature gives both causal slots the common output Fin 16 and leaves the anchor family empty.

**Definition 1.2 (Intervention finite realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/SharedArenaFiniteTemplates.interventionFiniteRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/SharedArenaFiniteTemplates.interventionFiniteRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The supplied functions are retained as the false and true readouts of the homogeneous signature.

**Definition 1.3 (Observation finite realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/SharedArenaFiniteTemplates.observationFiniteRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/SharedArenaFiniteTemplates.observationFiniteRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observation-intervention registrations use the same two-slot realization shape.

**Theorem 1.4 (Finite separation law).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/SharedArenaFiniteTemplates.finiteArena`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/SharedArenaFiniteTemplates.finiteArena` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The law records a pair of states that agree on the first readout and differ on the second.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SharedArenaFiniteTemplates.finiteArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SharedArenaFiniteTemplates.finiteSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SharedArenaFiniteTemplates.interventionFiniteRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SharedArenaFiniteTemplates.observationFiniteRealization`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/TheoremUnit](TheoremUnit.md)
