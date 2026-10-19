# Finite graph relabels preserve actual beam coordinates

## Abstract

Actual finite graph relabels transport edge fibers, beam endpoints and row colimits.

Let r : Relabel G H carry an actual vertex equivalence and an actual edge equivalence satisfying both endpoint equations. essential transports incoming and outgoing witnesses. For the finite row and beam APIs use the source-declared Fintype and DecidableEq instances; for history homeomorphisms use the declared discrete edge topologies. The original universes of vertices and edges are independent. No essentiality is required for the row-transition square itself.

reindex r z at w is z(r.vertex.symm w). outgoingEquiv bijects the outgoing EDGE fibers, including all parallel copies. reindex_adjacency and reindex_step therefore derive the stationary transition square from the graph isomorphism, and rowMap/rowEquiv transport the existing direct limit. Signed integer stages keep exactly the same cut.

The actual homeomorphism takes ray G alpha N to ray H (r.homeomorph alpha) N. Its endpoint is r.vertex(endpoint G alpha N). partsEquiv is an equivalence of the intrinsic ray subsets, not an equivalence merely of endpoints. endpointRow_image hence reindexes all multiplicities; image_atCut includes empty partitions. beam_coordinate and object_coordinate extend to actual beams and finite tagged families. imageObject reindexes its finite tags through ULift (Fin card), which changes no summand or multiplicity.

These equations supply the old and next relabels surrounding every positive RS/SR letter. ActualWordMatrixPath.relabel_adjacency consumes reindex_adjacency to construct the actual dyadic matrix path, and ActualRelabelResidue.actual_Q_mul_P uses adjacency_counted to identify its target counts. Thus the finite numbering changes in the arbitrary-h construction are justified by edge data rather than a postulated matrix conjugacy.

**Definition 1.1 (Transport actual incoming and outgoing witnesses through both endpoint equations.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.essential`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.essential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport actual incoming and outgoing witnesses through both endpoint equations.

**Definition 1.2 (Reindex every integral row by the inverse vertex bijection.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.reindex`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.reindex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reindex every integral row by the inverse vertex bijection.

**Theorem 1.3 (Reindex a single basis vector with its full integer coefficient.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.reindex_single`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.reindex_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindex a single basis vector with its full integer coefficient.

**Definition 1.4 (Transport each individual outgoing edge rather than just its endpoint.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.outgoingEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.outgoingEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport each individual outgoing edge rather than just its endpoint.

**Theorem 1.5 (Derive adjacency transport from the actual outgoing-edge bijection.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.reindex_adjacency`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.reindex_adjacency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derive adjacency transport from the actual outgoing-edge bijection.

**Theorem 1.6 (Derive the stationary transition square from counted edge data.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.reindex_step`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.reindex_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derive the stationary transition square from counted edge data.

**Theorem 1.7 (Iterate that square for every nonnegative transition power.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.reindex_power`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.reindex_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Iterate that square for every nonnegative transition power.

**Definition 1.8 (Construct the row-colimit map from the proved stationary transition square.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.rowMap`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.rowMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Construct the row-colimit map from the proved stationary transition square.

**Theorem 1.9 (Evaluate the direct-limit map on every original natural stage.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.rowMap_stage`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.rowMap_stage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluate the direct-limit map on every original natural stage.

**Theorem 1.10 (Evaluate it at every signed integer cut without changing that cut.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.rowMap_intStage`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.rowMap_intStage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluate it at every signed integer cut without changing that cut.

**Theorem 1.11 (Use the inverse vertex/edge relabel to recover every direct-limit class.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.rowMap_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.rowMap_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the inverse vertex/edge relabel to recover every direct-limit class.

**Definition 1.12 (Use the proved inverse identities to form the native Int-linear colimit equivalence.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.rowEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.rowEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the proved inverse identities to form the native Int-linear colimit equivalence.

**Theorem 1.13 (Map ray G alpha N by r.homeomorph to the single ray H (r.homeomorph alpha) N.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.image_ray`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.image_ray` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Map ray G alpha N by r.homeomorph to the single ray H (r.homeomorph alpha) N.

**Theorem 1.14 (Transport the endpoint at the exact corresponding cut.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.image_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.image_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport the endpoint at the exact corresponding cut.

**Definition 1.15 (Bijection the complete intrinsic partition as actual ray subsets.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.partsEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.partsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Bijection the complete intrinsic partition as actual ray subsets.

**Theorem 1.16 (Compute the endpoint of each transported intrinsic ray subset.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.parts_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.parts_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compute the endpoint of each transported intrinsic ray subset.

**Theorem 1.17 (Transport the whole intrinsic finite partition of an actual beam at its stated cut.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.image_atCut`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.image_atCut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport the whole intrinsic finite partition of an actual beam at its stated cut.

**Theorem 1.18 (Compute actual image endpoint multiplicities before passage to any row colimit.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.endpointRow_image`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.endpointRow_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compute actual image endpoint multiplicities before passage to any row colimit.

**Definition 1.19 (Bundle each literal history image with its proved beam partition.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.imageBeam`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.imageBeam` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Bundle each literal history image with its proved beam partition.

**Theorem 1.20 (Identify the native coordinate of every actual image beam.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.beam_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.beam_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identify the native coordinate of every actual image beam.

**Definition 1.21 (Transport the entire finite tagged family of actual beams.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.imageObject`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.imageObject` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport the entire finite tagged family of actual beams.

**Theorem 1.22 (Extend beam-coordinate compatibility by summing the original finite tagged family.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.object_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.object_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Extend beam-coordinate compatibility by summing the original finite tagged family.

**Definition 1.23 (Form the existing geometric group equivalence by the proved row-coordinate conjugacy.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.beamEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.beamEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Form the existing geometric group equivalence by the proved row-coordinate conjugacy.

**Theorem 1.24 (Compute the native coordinate of the complete beam-group equivalence.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.beamEquiv_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.beamEquiv_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compute the native coordinate of the complete beam-group equivalence.

**Theorem 1.25 (Identify the image of every finite tagged object with the actual transported object.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.beamEquiv_object`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.beamEquiv_object` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identify the image of every finite tagged object with the actual transported object.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.beamEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.beamEquiv_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.beamEquiv_object`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.beam_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.endpointRow_image`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.essential`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.imageBeam`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.imageObject`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.image_atCut`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.image_endpoint`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.image_ray`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.object_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.outgoingEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.partsEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.parts_endpoint`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.reindex`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.reindex_adjacency`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.reindex_power`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.reindex_single`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.reindex_step`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.rowEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.rowMap`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.rowMap_intStage`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.rowMap_inverse`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport.rowMap_stage`
- Dependency: [D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit](CountedMatrixBeamColimit.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord](../PositiveRecoding/TypedPositiveSplitWord.md)
