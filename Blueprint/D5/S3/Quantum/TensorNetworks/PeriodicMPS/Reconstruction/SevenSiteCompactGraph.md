# The ordinary chart of the compact seven-site trace graph

## Abstract

The ordinary chart of the compact seven-site trace graph

**Theorem 1.1 (The ordinary chart of the compact seven-site trace graph).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCompactGraph.image_traceChart`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCompactGraph.image_traceChart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compact trace graph pairs the projector of the six weighted invariant coordinates with the full seven-site trace-word projector. Its ordinary part is exactly the image of the four complex coordinates obtained by fixing the first trace to one and requiring a nonzero amplitude.

A nonzero first diagonal entry of the weighted projector lets the decoder recover the normalized trace coordinates. At a defined amplitude, the graph limit above the corresponding weighted projector is unique. The ordinary part is open, dense and path connected in the compact graph.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCompactGraph.image_traceChart`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSRegularComplement](../PeriodicMPSRegularComplement.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteTraceBase](SevenSiteTraceBase.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSProjectiveCoordinates](../../PeriodicMPSProjectiveCoordinates.md)
