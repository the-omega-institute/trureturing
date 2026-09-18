# PointwiseEqualityRegistrations

## Abstract

Exact pointwise registration programs over finite object states.

**Definition 1.1 (substitutionArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitutionArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitutionArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three substitution labels remain the states; both outputs are codes in Fin 3.

**Definition 1.2 (substitutionRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitutionRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitutionRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both readouts return the label code: zero denotes [large], one [large, small], and two [large, combined].

**Theorem 1.3 (substitution_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitution_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitution_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Encoding and reconstruction are checked separately for both original substitution expressions at every label. Code equality is equivalent to list equality on their occurring support; no injection on all lists is asserted.

**Theorem 1.4 (substitution_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitution_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitution_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen compatibility theorem satisfies the code law through the bridge; constant codes zero and one falsify it.

**Theorem 1.5 (substitution_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitution_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.substitution_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct Fin 3 codes zero and one witness independent sensitivity of both readout slots.

**Definition 1.6 (recenterReadout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenterReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenterReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constant Fin 2 zero code represents the integer origin for every direction; the same definition is used in the realization and declared readout.

**Definition 1.7 (recenterArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenterArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenterArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three directed neighbors remain the states, with Fin 2 output codes.

**Definition 1.8 (recenterRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenterRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenterRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both readouts use the zero code for the recentered neighbor and the integer origin.

**Theorem 1.9 (recenter_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenter_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenter_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge checks encoding and reconstruction of every recentered direction from the definitions. Zero decodes to (0, 0) and one to (1, 0); equality is transported on the occurring support without a global injection from integer pairs or use of the registered theorem.

**Theorem 1.10 (recenter_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenter_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenter_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen recenter theorem satisfies the code law through the bridge; distinct constant codes zero and one falsify it.

**Theorem 1.11 (recenter_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenter_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenter_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unused Fin 2 code one and origin code zero witness independent sensitivity of both readout slots.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenterArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations.recenterReadout`
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
