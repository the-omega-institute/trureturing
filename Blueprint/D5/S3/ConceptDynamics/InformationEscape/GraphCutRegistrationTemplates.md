# GraphCutRegistrationTemplates

## Abstract

A dependent signature types the full binary edge-gradient readout on arbitrary simple graphs.

**Definition 1.1 (Binary graph-gradient signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GraphCutRegistrationTemplates.graphGradientSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GraphCutRegistrationTemplates.graphGradientSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Parameters pair an arbitrary vertex type V with a SimpleGraph V. States are all binary vertex labelings V -> ZMod 2. The sole role is Unit, and its output is a binary word on the full edge set G.edgeSet; the anchor type is Empty. The signature imposes no finiteness condition on vertices or edges. The edge-connectivity consumer supplies Fintype G.edgeSet when it measures the Hamming weight of an edge gradient. Reg/D5/S3/Fourier/CharacterSelection/EdgeConnectivityGradientWeight uses this signature with edgeDifferential as the actual full-edge readout. The definition is an operand for that source-bound registration, not a theorem or a registration proof.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GraphCutRegistrationTemplates.graphGradientSignature`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/DependentFamily](DependentFamily.md)
- Dependency: [D5/S3/Fourier/CharacterSelection/SimpleGraphCycleSpace](../../Fourier/CharacterSelection/SimpleGraphCycleSpace.md)
