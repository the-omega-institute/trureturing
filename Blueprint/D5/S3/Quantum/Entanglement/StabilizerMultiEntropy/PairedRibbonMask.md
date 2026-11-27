# From an actual paired ribbon mask to normalized Bell amplitudes

## Abstract

The literal paired ribbon mask supplies a tensor Bell amplitude.

**Theorem 1.1 (The masked physical amplitude factors after the right Hadamards).**

$$\forall u \in \operatorname{LiteralInterlacedPairedRibbonMasks}\left(\right),\; \operatorname{NormalizedRightHadamardAmplitude}\left(u\right) = \operatorname{SignedTensorBellAmplitude}\left(u\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/PairedRibbonMask.literal_tensor_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Construct a cyclic gap involution and literal marked ports as consecutive four-port packets. A whole four-port packet contains two interlaced bands, with no interlacement to any other packet. Retain its twisted band. The actual protected masked phase factors into the local binary phase xy+xd+yc+tau cd. The chart mismatch between raw switch and oriented twist bits is handled before phase extraction.

Right Hadamards transform the normalized conditional phase into a product of Bell amplitudes, with one overall sign determined by the deleted twists and labels. The proof uses the literal band mask and not a postulated labelling of Bell states.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/PairedRibbonMask.literal_tensor_transport`
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonErasure](MarkedRibbonErasure.md)
