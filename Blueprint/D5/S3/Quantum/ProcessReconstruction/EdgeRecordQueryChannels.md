# Hidden-Input Channel Action

## Abstract

An arbitrary reference sees an exact trace norm error proportional to the probe mass on the hidden word.

**Theorem 1.1 (The exact change from the uniform reference oracle).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryChannels.referenceError_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryChannels.referenceError_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

For every joint probe and finite reference, the unhalved trace norm difference between the marked and uniform outputs equals the trace of the probe's positive reference block at the marked input. The channel is a deterministic specialization of Ghosh, Jackson and Datta, Equations (8)–(10).

**Theorem 1.2 (Opposite parities at a shared mark have diamond distance two).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryChannels.markedPair_diamond`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryChannels.markedPair_diamond` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

The computational probe at the mark attains the maximum unhalved diamond distance. The two open diamond balls of radius one are disjoint.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryChannels.markedPair_diamond`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryChannels.referenceError_exact`
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Foundation/FinitePreparationChannel](../Foundation/FinitePreparationChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/TraceNormTensorProduct](../Foundation/TraceNormTensorProduct.md)
