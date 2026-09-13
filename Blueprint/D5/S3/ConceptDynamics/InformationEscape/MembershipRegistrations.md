# MembershipRegistrations

## Abstract

Exact annihilator membership registrations over four frequencies.

These registrations retain classical annihilator membership. Finite sealing requires a computable readout and is not supplied; the registration diagnostics remain visible.

**Definition 1.1 (objectArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.objectArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.objectArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both frozen statements use the same four-frequency object arena and catalog.

**Definition 1.2 (memberArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.memberArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.memberArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positive polarity requires the anchor to belong to the supplied set.

**Definition 1.3 (nonmemberArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.nonmemberArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.nonmemberArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Negative polarity requires the anchor to lie outside the supplied set.

**Theorem 1.4 (member_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.member_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.member_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive law has independently checked membership-readout and anchor support.

**Theorem 1.5 (nonmember_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.nonmember_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.nonmember_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative law has independently checked membership-readout and anchor support.

**Definition 1.6 (twoRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.twoRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.twoRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original annihilator membership predicate is retained with anchor two, using classical decidability without theorem-based reduction.

**Theorem 1.7 (two_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.two_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.two_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge preserves the frozen statement that frequency two belongs to the annihilator.

**Theorem 1.8 (two_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.two_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.two_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen membership theorem satisfies the law; changing the anchor to one falsifies it by the frozen exclusion theorem.

**Definition 1.9 (oneRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.oneRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.oneRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same original annihilator membership predicate is retained with anchor one.

**Theorem 1.10 (one_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.one_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.one_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge preserves the frozen statement that frequency one does not belong to the annihilator.

**Theorem 1.11 (one_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.one_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.one_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen exclusion theorem satisfies the law; changing the anchor to two falsifies it by the frozen membership theorem.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.memberArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.member_slotSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.nonmemberArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.nonmember_slotSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.objectArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.oneRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.one_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.one_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.twoRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.two_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.two_lawSensitive`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrationTemplates](MembershipRegistrationTemplates.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog](../InformationEscapeHierarchy/StructuralCatalog.md)
- Dependency: [D5/S3/Fourier/FinitePoisson](../../Fourier/FinitePoisson.md)
