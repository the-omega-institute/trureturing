# PointwiseEqualityRegistrations

## Abstract

Exact pointwise registration programs over finite object states.

**Definition 1.1 (substitutionArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitutionArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitutionArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source state is the three-letter substitution label.

**Definition 1.2 (substitutionRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitutionRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitutionRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two readouts are the general and Tribonacci substitution expressions as stated.

**Theorem 1.3 (substitution_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitution_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitution_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge retains every label and both unreduced substitution expressions.

**Theorem 1.4 (substitution_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitution_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitution_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen compatibility theorem satisfies the law; empty and singleton readouts falsify it.

**Theorem 1.5 (substitution_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitution_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitution_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic sensitivity theorem supplies checked support for both readouts.

**Definition 1.6 (recenterArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenterArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenterArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source state is one of the three directed neighbors.

**Definition 1.7 (recenterRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenterRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenterRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readouts are the recentered neighbor and the integer origin.

**Theorem 1.8 (recenter_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenter_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenter_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge retains the source equation at every direction without replacing its left side using the proof.

**Theorem 1.9 (recenter_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenter_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenter_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen recenter theorem satisfies the law; distinct constant coordinates falsify it.

**Theorem 1.10 (recenter_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenter_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenter_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both coordinate readout slots have checked sensitivity witnesses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenterArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenterRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenter_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenter_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenter_slotSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitutionArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitutionRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitution_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitution_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitution_slotSensitive`
- Dependency: [D5/S0/Tower/DBonacci/Substitution](../../../S0/Tower/DBonacci/Substitution.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/PointwiseRegistrationTemplates](PointwiseRegistrationTemplates.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog](../InformationEscapeHierarchy/StructuralCatalog.md)
- Dependency: [D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates](../../StatisticalMechanics/HardCore/SquareGridCoordinates.md)
