# IffRegistrationTemplates

## Abstract

Boolean predicate registrations over finite object states.

**Definition 1.1 (iffSignature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two Boolean CUT readouts retain the two predicates in an iff statement.

**Definition 1.2 (iffRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The supplied predicates are converted to Boolean readouts without changing their expressions.

**Definition 1.3 (iffArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The law equates the two Boolean readouts at every state of the supplied finite arena.

**Theorem 1.4 (iffLegacy).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffLegacy`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffLegacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The universally quantified iff statement is proved equivalent to the generated pointwise law: the bridge rewrites each iff into an equality of decided Booleans, so the two sides are logically equivalent, not definitionally equal.

**Theorem 1.5 (iff_sensitivity).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iff_sensitivity`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iff_sensitivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An inhabited state and distinct Boolean values witness sensitivity of each readout slot.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffLegacy`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iff_sensitivity`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/PointwiseRegistrationTemplates](PointwiseRegistrationTemplates.md)
