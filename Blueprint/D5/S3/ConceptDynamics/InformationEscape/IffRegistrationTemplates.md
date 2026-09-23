# IffRegistrationTemplates

## Abstract

Boolean predicate registrations over finite object states.

**Definition 1.1 (iffSignature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The homogeneous pointwise equality signature at Bool supplies two Boolean CUT readouts and an empty anchor index.

**Definition 1.2 (iffRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two supplied Boolean functions feed homogeneousPointwiseEqRealization with the pinned Boolean equality dictionary. This contracts the iff API onto the homogeneous pointwise template; the older pointwiseEqRealization is unchanged.

**Definition 1.3 (iffArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The homogeneous pointwise equality arena equates both Boolean readouts at every state of the supplied finite arena.

**Theorem 1.4 (iffLegacy).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffLegacy`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffLegacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic predicate interface retains explicit named DecidablePred dictionaries dP and dQ, applied under the Boolean readout lambdas. Equality of decided Booleans is equivalent to the original universally quantified iff statement.

**Theorem 1.5 (iff_sensitivity).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iff_sensitivity`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iff_sensitivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The homogeneous pointwise sensitivity theorem uses an inhabited state and the distinct Boolean values false and true to witness each readout slot.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffLegacy`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iffSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates.iff_sensitivity`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/PointwiseRegistrationTemplates](PointwiseRegistrationTemplates.md)
