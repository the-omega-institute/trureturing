# PointwiseOrderRegistrations

## Abstract

Exact pointwise registration programs over finite object states.

**Definition 1.1 (lengthZero).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.lengthZero`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.lengthZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shared Fin 3 zero constant represents the strict lower bound in the realization and readout declaration.

**Definition 1.2 (lengthOne).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.lengthOne`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.lengthOne` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Fin 3 one constant encodes the substitution length of false.

**Definition 1.3 (lengthTwo).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.lengthTwo`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.lengthTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shared Fin 3 two constant encodes the substitution length of true and the weak upper bound.

**Definition 1.4 (objectArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.objectArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.objectArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both bounds quantify over the same Boolean substitution letter.

**Definition 1.5 (strictArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.strictArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.strictArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positivity law compares Fin 3 codes using the strict branch of the homogeneous order arena.

**Definition 1.6 (weakArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.weakArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.weakArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The upper bound compares Fin 3 codes using the weak branch over the same object arena.

**Theorem 1.7 (strict_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.strict_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.strict_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin 3 values zero and one witness sensitivity of both slots for the strict law.

**Theorem 1.8 (weak_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.weak_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.weak_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin 3 values zero and one witness sensitivity of both slots for the weak law.

**Definition 1.9 (lengthReadout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.lengthReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.lengthReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Boolean elimination returns Fin 3 code one at false and two at true; their natural values are the original substitution lengths.

**Definition 1.10 (positiveRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positiveRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positiveRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two readouts are the shared zero code and finite length code, also used by the explicit readout declaration.

**Theorem 1.11 (positive_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positive_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positive_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Boolean cases identify each length code's natural value with the original list length. The defining Fin order transports strict positivity in both directions.

**Theorem 1.12 (positive_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positive_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positive_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source theorem satisfies the strict code law through the bridge; equal zero codes falsify it.

**Definition 1.13 (upperRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.upperRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.upperRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two readouts are the finite length code and shared bound-two code, also used by the explicit readout declaration.

**Theorem 1.14 (upper_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.upper_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.upper_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Boolean cases identify each length code's natural value with the original list length. The defining Fin order transports the weak upper bound in both directions.

**Theorem 1.15 (upper_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.upper_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.upper_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source theorem satisfies the weak code law through the bridge; constant codes one and zero falsify it.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.lengthOne`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.lengthReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.lengthTwo`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.lengthZero`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.objectArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positiveRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positive_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positive_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.strictArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.strict_slotSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.upperRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.upper_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.upper_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.weakArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.weak_slotSensitive`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/EscapeRecord](EscapeRecord.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/PointwiseRegistrationTemplates](PointwiseRegistrationTemplates.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog](../InformationEscapeHierarchy/StructuralCatalog.md)
