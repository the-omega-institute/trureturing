# GuardedEqualityRegistrations

## Abstract

Guarded equality registration programs over complete finite object arenas.

**Definition 1.1 (modelXYCode).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.modelXYCode`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.modelXYCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shared constructor-written zero in Fin 3 is definitionally M_XY.

**Definition 1.2 (positiveFirstReadout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirstReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirstReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pinned finite equality with modelXYCode gives the original E_X guard on all three models.

**Definition 1.3 (positiveFirstArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirstArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirstArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All three candidate models remain in the arena.

**Definition 1.4 (positiveFirstRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirstRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirstRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit guarded template receives positiveFirstReadout, the model identity and constant modelXYCode, retaining the original guard and equality readouts.

**Theorem 1.5 (positiveFirst_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirst_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirst_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Iff.rfl identifies the generated law with the original E_X hypothesis and model equality to M_XY.

**Theorem 1.6 (positiveFirst_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirst_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirst_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen theorem satisfies the law; changing the model readout falsifies it at M_XY while keeping E_X fixed.

**Theorem 1.7 (positiveFirst_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirst_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirst_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shared sensitivity theorem checks independent support for the guard and both equality slots.

**Definition 1.8 (sourceZero).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.sourceZero`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.sourceZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shared zero in Fin 6 codes outerH2.

**Definition 1.9 (sourceOne).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.sourceOne`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.sourceOne` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shared one in Fin 6 codes outerH25.

**Definition 1.10 (dimension39Code).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.dimension39Code`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.dimension39Code` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Zero in Fin 2 codes the occurring dimension thirty-nine.

**Definition 1.11 (dimension40Code).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.dimension40Code`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.dimension40Code` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One in Fin 2 codes the occurring dimension forty and the right equality readout.

**Definition 1.12 (outerGuardReadout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerGuardReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerGuardReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Boolean dispatch on finite equality recognizes exactly sourceZero and sourceOne as outer groups.

**Definition 1.13 (outerDimensionReadout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimensionReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimensionReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Boolean dispatch selects dimension40Code for the two outer groups and dimension39Code for the four inner groups.

**Definition 1.14 (outerDimensionCodeArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimensionCodeArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimensionCodeArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin 6 re-coordinates all PhysicalSourceGroup states in order: outerH2, outerH25, oldInnerH2, oldInnerH25, newInnerH2, newInnerH25. The guarded equality outputs use Fin 2 dimension codes.

**Definition 1.15 (outerDimensionRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimensionRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimensionRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit guarded template uses the outer guard, the encoded dimension and constant dimension40Code on the full six-state arena.

**Theorem 1.16 (outerDimension_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimension_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimension_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Local encode and decode maps form PhysicalSourceGroup ≃ Fin 6 via decodeEncode and encodeDecode. guardDecoded preserves the guard; dimensionEncoded matches the finite table. encodeDimension and decodeDimension reconstruct every occurring dimension and forty through dimensionDecoded, fortyEncoded and fortyDecoded. outputIff reflects equality of these codes to equality of dimensions, and pointwise transports the quantified conditional law. No injection from all natural numbers into Fin 2 is asserted.

**Theorem 1.17 (outerDimension_lawSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimension_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimension_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen theorem satisfies the encoded law; replacing the dimension readout by zero falsifies it at source zero with its guard fixed. The conflicting output codes zero and one decode to thirty-nine and forty.

**Theorem 1.18 (outerDimension_slotSensitive).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimension_slotSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimension_slotSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shared sensitivity theorem checks independent support for the guard and both equality slots.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.dimension39Code`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.dimension40Code`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.modelXYCode`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimensionCodeArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimensionReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimensionRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimension_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimension_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerDimension_slotSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.outerGuardReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirstArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirstReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirstRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirst_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirst_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.positiveFirst_slotSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.sourceOne`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations.sourceZero`
- Dependency: [D5/S3/ConceptDynamics/ExperimentDesign/PositiveFirstExperimentIdentification](../ExperimentDesign/PositiveFirstExperimentIdentification.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates](GuardedEqualityRegistrationTemplates.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog](../InformationEscapeHierarchy/StructuralCatalog.md)
