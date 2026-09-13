# ExistentialWitnessRegistrationTemplates

## Abstract

Exact existential registration over complete finite witness assignments.

**Definition 1.1 (existentialWitnessSignature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates.existentialWitnessSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates.existentialWitnessSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A complete witness assignment is the state and its acceptance is the sole ADMIT slot.

**Definition 1.2 (existentialWitnessRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates.existentialWitnessRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates.existentialWitnessRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The supplied predicate is evaluated at each witness state without replacing it by a proved existential.

**Definition 1.3 (existentialWitnessArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates.existentialWitnessArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates.existentialWitnessArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed law requires an accepted state; no raw law or predicate is passed to the arena constructor.

**Theorem 1.4 (existentialWitnessLegacy).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates.existentialWitnessLegacy`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates.existentialWitnessLegacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Boolean reflection identifies existence of an accepted state with the full existential predicate.

**Theorem 1.5 (existentialWitness_sensitivity).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates.existentialWitness_sensitivity`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates.existentialWitness_sensitivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On any inhabited arena, all-accepted and all-rejected realizations witness sensitivity of the single slot.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates.existentialWitnessArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates.existentialWitnessLegacy`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates.existentialWitnessRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates.existentialWitnessSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates.existentialWitness_sensitivity`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/TheoremUnit](TheoremUnit.md)
