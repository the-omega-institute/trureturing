# Actual beam images in the native right-row colimit

## Abstract

Actual counted beam images and right-row colimit transport with the exact inverse cut.

Use the same natural matrices R : CountMat n m and S : CountMat m n and the existing RowLimit of the corresponding counted graphs. rowMap is the Module.DirectLimit.map induced by z -> z vecMul integerCounts R. Associativity gives (RS)R=R(SR) in the right-row orientation; neither a transpose nor injectivity of an original transition map is assumed.

At every integer cut N, rowMap sends intStage_RS N z to intStage_SR N (z R). rowInverse sends intStage_SR N w to intStage_RS (N+1) (w S). The extra +1 is essential: the reverse SAME-cut rowMap composes to Theta, whose signed-stage expression is N-1. The existing direct-limit relation identifies stage (N+1) (z RS) with stage N z, which supplies both inverse identities. This construction allows singular matrices and zero-dimensional stages.

For target essentiality hB, actual_ray_coordinate identifies the coordinate of the literal Set.image ray. For whole beams the source essentiality hA and target essentiality hB let beamCoordinate be evaluated at any representing cut. actual_beam_coordinate and actual_object_coordinate prove compatibility before elementaryBeamEquiv is defined by conjugating the existing beamRowEquiv. The object formula then shows that this conjugated equivalence really is the Set.image action on every tagged object; it is not an assumed geometric diagram.

PositiveWordBeamTransport consumes the constructed row equivalence for each positive letter and the actual beam and endpoint suppliers for literal images. Together these reach the native h action through the constructed original-domain word. They provide the coordinate bridge; the periodic cochain identity, orbit counts, literal forward Fix6 factorization and same-character minimum-six obstruction are separate ingredients of the preserved accepted original application.

**Definition 1.1 (Construct the row-colimit map from the proved stationary transition square.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowMap`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Construct the row-colimit map from the proved stationary transition square.

**Theorem 1.2 (Evaluate the direct-limit map on every original natural stage.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowMap_stage`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowMap_stage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluate the direct-limit map on every original natural stage.

**Theorem 1.3 (Evaluate it at every signed integer cut without changing that cut.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowMap_intStage`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowMap_intStage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluate it at every signed integer cut without changing that cut.

**Definition 1.4 (Construct the inverse using S at the NEXT target cut.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowInverse`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Construct the inverse using S at the NEXT target cut.

**Theorem 1.5 (The inverse maps (N,w) to (N+1,w S).).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowInverse_stage`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowInverse_stage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse maps (N,w) to (N+1,w S).

**Theorem 1.6 (Use the actual direct-limit stage relation to recover every source class.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowInverse_left`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowInverse_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the actual direct-limit stage relation to recover every source class.

**Theorem 1.7 (Use the same relation to recover every target class.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowInverse_right`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowInverse_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the same relation to recover every target class.

**Definition 1.8 (Use the proved inverse identities to form the native Int-linear colimit equivalence.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the proved inverse identities to form the native Int-linear colimit equivalence.

**Theorem 1.9 (Derive the native coordinate of the literal image ray from its numbered endpoint partition.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.actual_ray_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.actual_ray_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derive the native coordinate of the literal image ray from its numbered endpoint partition.

**Theorem 1.10 (Extend the actual cross-graph coordinate diagram to every intrinsic finite beam.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.actual_beam_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.actual_beam_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Extend the actual cross-graph coordinate diagram to every intrinsic finite beam.

**Definition 1.11 (Take actual elementary images of all beams, keeping the finite tag multiplicities.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.elementaryImageObject`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.elementaryImageObject` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take actual elementary images of all beams, keeping the finite tag multiplicities.

**Theorem 1.12 (Sum the proved beam coordinates over the complete tagged object.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.actual_object_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.actual_object_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sum the proved beam coordinates over the complete tagged object.

**Definition 1.13 (Conjugate the native row equivalence only after actual subset compatibility is established.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.elementaryBeamEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.elementaryBeamEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugate the native row equivalence only after actual subset compatibility is established.

**Theorem 1.14 (Compute the forward coordinate of the resulting existing beam-group equivalence.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.elementaryBeamEquiv_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.elementaryBeamEquiv_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compute the forward coordinate of the resulting existing beam-group equivalence.

**Theorem 1.15 (Prove that every tagged object is sent to its literal Set.image object.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.elementaryBeamEquiv_object`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.elementaryBeamEquiv_object` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Prove that every tagged object is sent to its literal Set.image object.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.actual_beam_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.actual_object_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.actual_ray_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.elementaryBeamEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.elementaryBeamEquiv_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.elementaryBeamEquiv_object`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.elementaryImageObject`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowInverse`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowInverse_left`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowInverse_right`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowInverse_stage`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowMap`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowMap_intStage`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit.rowMap_stage`
- Dependency: [D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram](CountedMatrixBeamDiagram.md)
