# MapInjectiveRegistrations

## Abstract

Three frozen maps share one exact injectivity registration template.

**Definition 1.1 (markerArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.markerArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.markerArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The state and output are Fin 2, giving finite coordinates for the two source markers.

**Definition 1.2 (markerRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.markerRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.markerRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The identity readout on Fin 2 uses the enrolled mapInjectiveRealization template with instDecidableEqFin 2.

**Theorem 1.3 (marker_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge retains Function.Injective markerDigit verbatim. Local encode and decode maps follow the original digits and constructor order; inverse identities and equality of encoded values transport injectivity in both directions.

**Theorem 1.4 (marker_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen injectivity theorem satisfies the law through the bridge; a constant readout identifies finite coordinates zero and one.

**Theorem 1.5 (marker_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic sensitivity theorem checks the identity CUT slot on Fin 2.

**Definition 1.6 (opcodeArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcodeArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcodeArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The state and output are Fin 12, giving finite coordinates for the twelve source operation codes.

**Definition 1.7 (opcodeRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcodeRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcodeRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The identity readout on Fin 12 uses the enrolled mapInjectiveRealization template with instDecidableEqFin 12.

**Theorem 1.8 (opcode_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcode_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcode_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge retains Function.Injective opcodeIndex verbatim. Local encode and decode maps follow the original indices and constructor order; inverse identities and equality of encoded values transport injectivity in both directions.

**Theorem 1.9 (opcode_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcode_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcode_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen injectivity theorem satisfies the law through the bridge; a constant readout identifies finite coordinates zero and one.

**Theorem 1.10 (opcode_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcode_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcode_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic sensitivity theorem checks the identity CUT slot on Fin 12.

**Definition 1.11 (rayArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.rayArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.rayArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source state is one of the eighteen ray labels, with output in Fin 81.

**Definition 1.12 (rayRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.rayRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.rayRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout shifts the four ksVectors coordinates by one and packs them as four ternary digits in Fin 81.

**Theorem 1.13 (ray_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.ray_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.ray_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge retains Function.Injective ksVectors verbatim.

**Theorem 1.14 (ray_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.ray_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.ray_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen injectivity theorem satisfies the law; the constant zeroth ray code identifies ray labels zero and one.

**Theorem 1.15 (ray_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.ray_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.ray_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic sensitivity theorem checks the encoded ray CUT slot.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.markerArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.markerRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_slotSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.opcodeArena`
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
