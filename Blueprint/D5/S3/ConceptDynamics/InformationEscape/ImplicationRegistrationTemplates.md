# ImplicationRegistrationTemplates

## Abstract

Exact implication registration programs over finite object states.

**Definition 1.1 (implicationSignature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates.implicationSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates.implicationSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two CUT slots retain finite Boolean functions for the antecedent and consequent independently.

**Definition 1.2 (implicationRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates.implicationRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates.implicationRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each predicate is evaluated at the current arena state and finite index, then reflected by decide; no source theorem is used.

**Definition 1.3 (implicationArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates.implicationArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates.implicationArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At every state and index, the fixed law requires the consequent whenever the antecedent holds. No arbitrary law is accepted.

**Theorem 1.4 (implicationLegacy).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates.implicationLegacy`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates.implicationLegacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Boolean reflection preserves every state and both predicates of the complete implication.

**Theorem 1.5 (implication_sensitivity).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates.implication_sensitivity`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates.implication_sensitivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the arena and index are inhabited, switching either Boolean-function readout alone changes the law while the other slot remains fixed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates.implicationArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates.implicationLegacy`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates.implicationRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates.implicationSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates.implication_sensitivity`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/TheoremUnit](TheoremUnit.md)
