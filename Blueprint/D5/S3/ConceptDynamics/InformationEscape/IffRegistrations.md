# IffRegistrations

## Abstract

Exact iff registrations over finite object states.

**Definition 1.1 (unsettledCode).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.unsettledCode`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.unsettledCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shared constructor-written zero in Fin 5 codes the unsettled claim.

**Definition 1.2 (openPermissionReadout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.openPermissionReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.openPermissionReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pinned finite equality with unsettledCode gives the Boolean table for open-outcome permission after decoding each claim.

**Definition 1.3 (openUnsettledReadout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.openUnsettledReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.openUnsettledReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pinned finite equality with unsettledCode gives the Boolean table for the decoded claim being unsettled.

**Definition 1.4 (openCodeArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.openCodeArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.openCodeArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin 5 re-coordinates every Claim in order: unsettled, nonformalJudgment, consequentUnderConditions, assertP, assertNegP. All four non-unsettled claims remain in the arena.

**Definition 1.5 (openRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.openRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.openRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit iff template receives separate permission and unsettled Boolean readouts on all five codes.

**Theorem 1.6 (open_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.open_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.open_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Local encode and decode maps form Claim ≃ Fin 5 via decodeEncode and encodeDecode. leftDecoded and rightDecoded independently identify the readouts with the decided original permission and unsettled predicates at every code. pointwise uses Bool.eq_iff_iff to transport Boolean equality to the original iff, and the coordinate equivalence transports its universal quantifier.

**Theorem 1.7 (open_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.open_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.open_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen open-permission characterization satisfies the encoded law; constant true and false readouts falsify it at the unsettled code.

**Theorem 1.8 (open_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.open_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.open_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both Boolean readout slots have checked sensitivity witnesses.

**Definition 1.9 (dualFixedReadout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dualFixedReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dualFixedReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pinned Boolean equality compares both coordinates of a Convention to read duality fixedness.

**Definition 1.10 (dualAlternativesReadout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dualAlternativesReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dualAlternativesReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Bool.rec selects the second coordinate's equality to false or true according to the first coordinate, reading the FvF or AvA alternatives.

**Definition 1.11 (dualArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dualArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dualArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source state is one of the four Boolean tie-breaking conventions.

**Definition 1.12 (dualRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dualRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dualRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit iff template receives dualFixedReadout and dualAlternativesReadout on the unchanged Convention carrier.

**Theorem 1.13 (dual_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dual_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dual_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

leftIff and rightIff independently check fixedness and the FvF or AvA alternatives in all four Boolean cases. pointwise uses Bool.eq_iff_iff to identify equality of the readouts with the original iff, without using dual_fixed_iff inside the bridge.

**Theorem 1.14 (dual_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dual_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dual_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen dual-fixed characterization satisfies the law; constant true and false readouts falsify it.

**Theorem 1.15 (dual_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dual_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dual_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both Boolean readout slots have checked sensitivity witnesses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dualAlternativesReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dualArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dualFixedReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dualRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dual_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dual_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dual_slotSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.openCodeArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.openPermissionReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.openRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.openUnsettledReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.open_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.open_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.open_slotSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.unsettledCode`
- Dependency: [D5/S0/Certificates/SelfInterestConventionDeviationGain](../../../S0/Certificates/SelfInterestConventionDeviationGain.md)
- Dependency: [D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling](../Answering/AssertionSettlementCeiling.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates](IffRegistrationTemplates.md)
- Dependency: [D5/S3/ConceptDynamics/RegistrationWitnesses](../RegistrationWitnesses.md)
