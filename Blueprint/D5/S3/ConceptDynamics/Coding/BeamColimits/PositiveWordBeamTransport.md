# Dependent positive words transport actual beam coordinates

## Abstract

Dependent positive words transport actual beams and integer endpoint rows functorially.

Word F H is the existing endpoint-indexed finite syntax: a graph relabel, a positive counted RS/SR letter bracketed by old/next relabels, or composition. F and H are full finite essential presentations with their own edge topologies. There is no arbitrary-history-map, inverse or time leaf. In a composition first then second, evaluation and transport apply first before second.

endpointMap sends a relabel to reindex; a positive letter to reindex(next) after right multiplication by R after reindex(old.symm); composition to endpointMap(second).comp(endpointMap(first)). rowEquiv uses the matching existing colimit equivalences in that order. rowEquiv_intStage holds for EVERY signed N and every integral row, before choosing beam representatives.

imageBeam is recursively an actual image beam, and imageBeam_val proves its subset is exactly w.eval image U. image_atCut leaves the cut N unchanged for every positive constructor. endpointRow_image proves equality of the integer endpoint rows themselves, before a possibly noninjective map into the colimit. Empty beams, degenerate presentations and zero matrix fibers remain in the dependent syntax; no all-fibers nonconstant hypothesis is imposed.

beam_coordinate is the consumed compatibility for literal images used inside PositiveWordFullAction.full_action_coordinate. ActualWordMatrixPath.endpointMap_cast consumes the exact integer endpointMap to compare it with the dyadic path on the same original numbering. The arbitrary native h enters via OriginalPositiveWordAssembly.positive_word, whose full input tower, finite numbered identification and response-output word give an actual Word P P and a derived integer correction. This is the bridge to arithmetic, not a replacement of h by an unrelated character.

**Definition 1.1 (Recursively compose relabel row maps and right multiplication by each positive R.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.endpointMap`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.endpointMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Recursively compose relabel row maps and right multiplication by each positive R.

**Definition 1.2 (Use the proved inverse identities to form the native Int-linear colimit equivalence.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.rowEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.rowEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the proved inverse identities to form the native Int-linear colimit equivalence.

**Theorem 1.3 (At every signed cut, the complete dependent word acts by its exact integral endpointMap.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.rowEquiv_intStage`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.rowEquiv_intStage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every signed cut, the complete dependent word acts by its exact integral endpointMap.

**Definition 1.4 (Bundle each literal history image with its proved beam partition.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.imageBeam`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.imageBeam` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Bundle each literal history image with its proved beam partition.

**Theorem 1.5 (The recursive beam construction has literally the Set.image subset w.eval image U.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.imageBeam_val`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.imageBeam_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recursive beam construction has literally the Set.image subset w.eval image U.

**Theorem 1.6 (Transport the whole intrinsic finite partition of an actual beam at its stated cut.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.image_atCut`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.image_atCut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport the whole intrinsic finite partition of an actual beam at its stated cut.

**Theorem 1.7 (Compute actual image endpoint multiplicities before passage to any row colimit.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.endpointRow_image`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.endpointRow_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compute actual image endpoint multiplicities before passage to any row colimit.

**Theorem 1.8 (Identify the native coordinate of every actual image beam.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.beam_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.beam_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identify the native coordinate of every actual image beam.

**Definition 1.9 (Transport the entire finite tagged family of actual beams.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.imageObject`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.imageObject` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport the entire finite tagged family of actual beams.

**Theorem 1.10 (Extend beam-coordinate compatibility by summing the original finite tagged family.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.object_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.object_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Extend beam-coordinate compatibility by summing the original finite tagged family.

**Definition 1.11 (Form the existing geometric group equivalence by the proved row-coordinate conjugacy.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.beamEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.beamEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Form the existing geometric group equivalence by the proved row-coordinate conjugacy.

**Theorem 1.12 (Compute the native coordinate of the complete beam-group equivalence.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.beamEquiv_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.beamEquiv_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compute the native coordinate of the complete beam-group equivalence.

**Theorem 1.13 (Identify the image of every finite tagged object with the actual transported object.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.beamEquiv_object`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.beamEquiv_object` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identify the image of every finite tagged object with the actual transported object.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.beamEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.beamEquiv_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.beamEquiv_object`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.beam_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.endpointMap`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.endpointRow_image`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.imageBeam`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.imageBeam_val`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.imageObject`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.image_atCut`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.object_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.rowEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport.rowEquiv_intStage`
- Dependency: [D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport](FiniteRelabelBeamTransport.md)
