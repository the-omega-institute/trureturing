# Signed time subtracts from actual beam cuts

## Abstract

Signed time transports actual beam cuts by subtraction on the existing row colimit.

For an arbitrary Int-module M and any endomorphism T, cutShift T s is a map on the EXISTING stationary direct limit. It sends intStage T N z to intStage T (N-s) z for all integers N and s. No injectivity or invertibility of T on M is required. cutShift T (-s) is its inverse on the colimit, so cutEquiv is derived rather than assumed.

For an actual finite discrete-edge graph G, timeHomeomorph G s is the existing translate: (translate G s x)(k)=x(k+s). Hence its literal ray image has cut N-s and the SAME endpoint. partsEquiv transports every intrinsic ray subset to that cut, and endpointRow_image preserves the full integer endpoint row. This includes negative cuts and the empty beam, rather than restricting to nonnegative time.

With Essential G, beam_coordinate identifies actual time on any beam with cutShift on its row coordinate. In the arbitrary-h application s=-a-((a+c)+(b+d+1)) is derived by the original response/tower construction. PositiveWordFullAction therefore acts first by the same-cut word equivalence and then by cutShift s. On stage zero this is intStage (-s) of endpointMap w z; this exact sign feeds the native inverse power in OriginalRootKernelCheck.

The forward convention is unchanged throughout: translating histories forward by +1 moves the cut to N-1. The source formulas distinguish a reverse positive letter from the actual inverse; the latter needs its extra cut correction. The integer action is on the colimit even for singular original stage maps.

**Definition 1.1 (Lift signed cut subtraction to the existing stationary direct limit for an arbitrary endomorphism.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.cutShift`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.cutShift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lift signed cut subtraction to the existing stationary direct limit for an arbitrary endomorphism.

**Theorem 1.2 (Evaluate cut subtraction on each natural stage.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.cutShift_stage`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.cutShift_stage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluate cut subtraction on each natural stage.

**Theorem 1.3 (Subtract s from EVERY integer cut N, including negative cuts.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.cutShift_intStage`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.cutShift_intStage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtract s from EVERY integer cut N, including negative cuts.

**Theorem 1.4 (Negating s gives the inverse on the direct limit, without assuming the stage map invertible.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.cutShift_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.cutShift_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Negating s gives the inverse on the direct limit, without assuming the stage map invertible.

**Definition 1.5 (Use the two inverse laws to make the actual Int-linear colimit equivalence.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.cutEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.cutEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the two inverse laws to make the actual Int-linear colimit equivalence.

**Definition 1.6 (Use translate s with its continuous inverse translate (-s) on all legal histories.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.timeHomeomorph`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.timeHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use translate s with its continuous inverse translate (-s) on all legal histories.

**Theorem 1.7 (Map ray G alpha N by timeHomeomorph G s to the single ray G (translate G s alpha) (N-s).).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.image_ray`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.image_ray` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Map ray G alpha N by timeHomeomorph G s to the single ray G (translate G s alpha) (N-s).

**Theorem 1.8 (Transport the endpoint at the exact corresponding cut.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.image_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.image_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport the endpoint at the exact corresponding cut.

**Definition 1.9 (Bijection the complete intrinsic partition as actual ray subsets.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.partsEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.partsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Bijection the complete intrinsic partition as actual ray subsets.

**Theorem 1.10 (Compute the endpoint of each transported intrinsic ray subset.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.parts_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.parts_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compute the endpoint of each transported intrinsic ray subset.

**Theorem 1.11 (Transport the whole intrinsic finite partition of an actual beam at its stated cut.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.image_atCut`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.image_atCut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport the whole intrinsic finite partition of an actual beam at its stated cut.

**Theorem 1.12 (Compute actual image endpoint multiplicities before passage to any row colimit.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.endpointRow_image`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.endpointRow_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compute actual image endpoint multiplicities before passage to any row colimit.

**Definition 1.13 (Bundle each literal history image with its proved beam partition.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.imageBeam`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.imageBeam` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Bundle each literal history image with its proved beam partition.

**Theorem 1.14 (Identify the native coordinate of every actual image beam.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.beam_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.beam_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identify the native coordinate of every actual image beam.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.beam_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.cutEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.cutShift`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.cutShift_intStage`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.cutShift_inverse`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.cutShift_stage`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.endpointRow_image`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.imageBeam`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.image_atCut`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.image_endpoint`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.image_ray`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.partsEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.parts_endpoint`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation.timeHomeomorph`
- Dependency: [D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport](PositiveWordBeamTransport.md)
