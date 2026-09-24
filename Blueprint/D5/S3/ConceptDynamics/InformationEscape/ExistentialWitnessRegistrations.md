# ExistentialWitnessRegistrations

## Abstract

Exact existential registration over complete finite witness assignments.

**Definition 1.1 (capturedArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.capturedArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.capturedArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All eight twist and listing assignments form the witness arena.

**Definition 1.2 (capturedRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.capturedRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.capturedRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Acceptance retains the negated IsEscaped predicate at each twist and listing.

**Theorem 1.3 (captured_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.captured_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.captured_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original two existential binders are bundled into a pair using only product existential equivalence and Boolean reflection.

**Theorem 1.4 (captured_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.captured_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.captured_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen captured-listing theorem validates the original realization; rejecting every assignment falsifies the law.

**Theorem 1.5 (captured_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.captured_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.captured_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic witness-template sensitivity theorem certifies the ADMIT slot.

**Definition 1.6 (recognitionArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.recognitionArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.recognitionArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All 64 concept and value assignments form the witness arena.

**Definition 1.7 (recognitionRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.recognitionRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.recognitionRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Acceptance retains both concept inequality and the original mutual-recognition predicate.

**Theorem 1.8 (recognition_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.recognition_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.recognition_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All four existential binders and both conjuncts are preserved by product bundling and Boolean reflection.

**Theorem 1.9 (recognition_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.recognition_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.recognition_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen unequal-concepts theorem validates acceptance; the all-rejected realization falsifies the law.

**Theorem 1.10 (recognition_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.recognition_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.recognition_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The single ADMIT slot has a checked generic sensitivity witness.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.capturedArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.capturedRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.captured_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.captured_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.captured_slotSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.recognitionArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.recognitionRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.recognition_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.recognition_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.recognition_slotSensitive`
- Dependency: [D5/S0/Diagonal/Lawvere/QualitativeEscape](../../../S0/Diagonal/Lawvere/QualitativeEscape.md)
- Dependency: [D5/S3/ConceptDynamics/Communication/MutualRecognitionIsJointRealizability](../Communication/MutualRecognitionIsJointRealizability.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates](ExistentialWitnessRegistrationTemplates.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog](../InformationEscapeHierarchy/StructuralCatalog.md)
- Dependency: [D5/S3/ConceptDynamics/RegistrationWitnesses](../RegistrationWitnesses.md)
