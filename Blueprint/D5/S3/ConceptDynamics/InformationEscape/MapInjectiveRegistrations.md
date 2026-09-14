# MapInjectiveRegistrations

## Abstract

Three frozen maps share one exact injectivity registration template.

**Definition 1.1 (markerFintype).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.markerFintype`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.markerFintype` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The local finite enumeration contains exactly the two source markers.

**Definition 1.2 (markerArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.markerArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.markerArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source state is a Marker, with natural-number output.

**Definition 1.3 (markerRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.markerRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.markerRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout is the frozen markerDigit map without reduction by its injectivity proof.

**Theorem 1.4 (marker_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge retains Function.Injective markerDigit verbatim.

**Theorem 1.5 (marker_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen injectivity theorem satisfies the law; a constant readout identifies the two distinct markers.

**Theorem 1.6 (marker_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic sensitivity theorem checks the marker-digit CUT slot.

**Definition 1.7 (opcodeFintype).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcodeFintype`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcodeFintype` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The local finite enumeration contains exactly the twelve source operation codes.

**Definition 1.8 (opcodeArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcodeArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcodeArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source state is an Opcode, with natural-number output.

**Definition 1.9 (opcodeRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcodeRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcodeRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete opcodeIndex map is the only readout.

**Theorem 1.10 (opcode_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcode_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcode_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge retains Function.Injective opcodeIndex verbatim.

**Theorem 1.11 (opcode_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcode_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcode_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen injectivity theorem satisfies the law; a constant map identifies the distinct gen and enc codes.

**Theorem 1.12 (opcode_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcode_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcode_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic sensitivity theorem checks the opcode-index CUT slot.

**Definition 1.13 (rayArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.rayArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.rayArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source state is one of the eighteen ray labels, with integer-vector output.

**Definition 1.14 (rayRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.rayRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.rayRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout is the unchanged ksVectors map into four integer coordinates.

**Theorem 1.15 (ray_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.ray_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.ray_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge retains Function.Injective ksVectors verbatim.

**Theorem 1.16 (ray_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.ray_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.ray_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen injectivity theorem satisfies the law; the constant zeroth vector identifies ray labels zero and one.

**Theorem 1.17 (ray_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.ray_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.ray_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic sensitivity theorem checks the integer-vector CUT slot.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.markerArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.markerFintype`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.markerRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_slotSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcodeArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcodeFintype`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcodeRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcode_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcode_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcode_slotSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.rayArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.rayRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.ray_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.ray_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.ray_slotSensitive`
- Dependency: [D5/S0/History/Coding/EventCodeIntertranslation](../../../S0/History/Coding/EventCodeIntertranslation.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrationTemplates](MapInjectiveRegistrationTemplates.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog](../InformationEscapeHierarchy/StructuralCatalog.md)
- Dependency: [D5/S3/QuantumContext/ProjectionValuationObstruction](../../QuantumContext/ProjectionValuationObstruction.md)
