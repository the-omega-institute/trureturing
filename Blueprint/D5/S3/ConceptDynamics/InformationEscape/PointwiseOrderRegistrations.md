# PointwiseOrderRegistrations

## Abstract

Exact pointwise registration programs over finite object states.

**Definition 1.1 (objectArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.objectArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.objectArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both bounds quantify over the same Boolean substitution letter.

**Definition 1.2 (strictArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.strictArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.strictArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positivity law uses the strict branch of the order template.

**Definition 1.3 (weakArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.weakArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.weakArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The upper bound uses the weak branch over the same object arena.

**Theorem 1.4 (strict_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.strict_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.strict_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both slots carry checked sensitivity for the strict law.

**Theorem 1.5 (weak_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.weak_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.weak_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both slots carry checked sensitivity for the weak law.

**Definition 1.6 (positiveRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positiveRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positiveRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readouts retain zero and the stated substitution length.

**Theorem 1.7 (positive_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positive_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positive_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge preserves positivity at every Boolean letter.

**Theorem 1.8 (positive_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positive_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.positive_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source theorem satisfies the strict law; equal zero readouts falsify it.

**Definition 1.9 (upperRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.upperRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.upperRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readouts retain the stated substitution length and the bound two.

**Theorem 1.10 (upper_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.upper_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.upper_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge preserves the upper bound at every Boolean letter.

**Theorem 1.11 (upper_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.upper_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations.upper_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source theorem satisfies the weak law; readouts one and zero falsify it.

## References

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
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/PointwiseRegistrationTemplates](PointwiseRegistrationTemplates.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog](../InformationEscapeHierarchy/StructuralCatalog.md)
