# PointwiseDisequalityRegistrations

## Abstract

Exact pointwise registration programs over finite object states.

**Definition 1.1 (digitZero).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.digitZero`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.digitZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Fin 4 zero constant is shared by the recurrent table and the transient exclusion readout.

**Definition 1.2 (digitOne).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.digitOne`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.digitOne` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Fin 4 one constant is the transient table value at input zero.

**Definition 1.3 (digitTwo).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.digitTwo`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.digitTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Fin 4 two constant is shared by the recurrent table decision and its excluded readout.

**Definition 1.4 (digitArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.digitArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.digitArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both channel exclusions use the same four-digit object arena and homogeneous Fin 4 outputs.

**Theorem 1.5 (digit_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.digit_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.digit_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both readout slots carry checked sensitivity using digits zero and one.

**Definition 1.6 (recurrentReadout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.recurrentReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.recurrentReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Boolean elimination implements the table [0, 1, 0, 3] on inputs [0, 1, 2, 3], replacing only digit two by zero.

**Definition 1.7 (recurrentRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.recurrentRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.recurrentRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The table readout and shared excluded digit two are the two homogeneous outputs, also used by the explicit readout declaration.

**Theorem 1.8 (recurrent_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.recurrent_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.recurrent_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Checking all four inputs proves the table equals the original recurrent retraction; rewriting this identity recovers the original disequality at every digit.

**Theorem 1.9 (recurrent_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.recurrent_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.recurrent_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source theorem satisfies the table law through the bridge; two constant digit-two readouts falsify it.

**Definition 1.10 (transientReadout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.transientReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.transientReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Boolean elimination implements the table [1, 1, 2, 3] on inputs [0, 1, 2, 3], replacing only zero by one.

**Definition 1.11 (transientRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.transientRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.transientRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The table readout and shared excluded digit zero are the two homogeneous outputs, also used by the explicit readout declaration.

**Theorem 1.12 (transient_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.transient_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.transient_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Checking all four inputs proves the table equals the original transient retraction; rewriting this identity recovers the original disequality at every digit.

**Theorem 1.13 (transient_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.transient_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.transient_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source theorem satisfies the table law through the bridge; two constant zero readouts falsify it.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.digitArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.digitOne`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.digitTwo`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.digitZero`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.digit_slotSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.recurrentReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.recurrentRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.recurrent_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.recurrent_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.transientReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.transientRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.transient_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.transient_lawSensitive`
- Dependency: [D5/S0/Certificates/SkeletonChannelRetraction](../../../S0/Certificates/SkeletonChannelRetraction.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/PointwiseRegistrationTemplates](PointwiseRegistrationTemplates.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog](../InformationEscapeHierarchy/StructuralCatalog.md)
