# CardinalityRegistrations

## Abstract

Exact cardinality registration programs over finite object states.

**Definition 1.1 (cognitiveArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.cognitiveArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.cognitiveArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The arena retains CognitiveState as the finite source state and 6 as the target.

**Definition 1.2 (cognitiveRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.cognitiveRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.cognitiveRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every source state is admitted through the single Boolean slot.

**Theorem 1.3 (cognitive_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.cognitive_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.cognitive_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge retains Fintype.card CognitiveState = 6 without substituting the frozen theorem into the statement.

**Theorem 1.4 (cognitive_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.cognitive_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.cognitive_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing frozen cardinality theorem satisfies the all-state law; empty admission falsifies it.

**Theorem 1.5 (cognitive_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.cognitive_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.cognitive_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic sensitivity theorem supplies the checked support of the ADMIT slot.

**Definition 1.6 (sourceGroupsArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.sourceGroupsArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.sourceGroupsArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The arena retains PhysicalSourceGroup as the finite source state and 6 as the target.

**Definition 1.7 (sourceGroupsRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.sourceGroupsRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.sourceGroupsRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every source state is admitted through the single Boolean slot.

**Theorem 1.8 (sourceGroups_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.sourceGroups_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.sourceGroups_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge retains Fintype.card PhysicalSourceGroup = 6 without substituting the frozen theorem into the statement.

**Theorem 1.9 (sourceGroups_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.sourceGroups_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.sourceGroups_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing frozen cardinality theorem satisfies the all-state law; empty admission falsifies it.

**Theorem 1.10 (sourceGroups_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.sourceGroups_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.sourceGroups_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic sensitivity theorem supplies the checked support of the ADMIT slot.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.cognitiveArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.cognitiveRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.cognitive_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.cognitive_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.cognitive_slotSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.sourceGroupsArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.sourceGroupsRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.sourceGroups_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.sourceGroups_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrations.sourceGroups_slotSensitive`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrationTemplates](CardinalityRegistrationTemplates.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog](../InformationEscapeHierarchy/StructuralCatalog.md)
- Dependency: [D5/S3/ObserverMemory/FiniteForgettingCertificate](../../ObserverMemory/FiniteForgettingCertificate.md)
