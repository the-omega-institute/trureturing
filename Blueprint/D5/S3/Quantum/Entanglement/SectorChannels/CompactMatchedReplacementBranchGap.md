# Compact Matched Replacement Branch Gap

## Abstract

Matched replacement on the compact rank-one flat carrier separates the generalized physical strategies by shared-classical branch count.

**Theorem 1.1 (A physical benchmark with a dimension-dependent branch lower bound).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/CompactMatchedReplacementBranchGap.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SectorChannels/CompactMatchedReplacementBranchGap.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m positive, encode the actual compact flat rank-one sectors by the isometry which copies the sector label to both physical parties. Construct a replacement channel with m shared branches. Each branch deterministically prepares the same chosen label on both sides, with weight 1/m. The construction uses native trace-preserving completely positive channels and their full-matrix mixture realization.

Any competitor with r shared classical product branches acts on the encoded basis witness as a weighted mixture of product states. Computational-basis measurement gives a mixture of pairs of independent local distributions. Their overlap with the uniformly matched label distribution is at most the square root of r/m, by capped arithmetic-geometric mean and Cauchy-Schwarz. Diagonal measurement cannot increase the trace norm, so the native unhalved diamond distance is at least twice one minus the square root of r/m.

The lower bound concerns approximation of this specific attainable replacement channel. It does not change the previously established optimum for the original coherent flat target, and the replacement operation does not impose exact-output calibration on every logical basis sector.

The exact distance in the paper consequence follows from `D5/S3/Quantum/Entanglement/SectorChannels/WeightedBinaryReplacementExact.replacer_diamond_exact`.

Paper consequence, not an additional Lean claim: if m equals r times k squared, choose r equiprobable branches supported on disjoint k-label blocks, with both local preparations independently uniform on their branch's block. The distance is exactly twice one minus 1/k, meeting the lower bound. In particular four matched labels have distance exactly one from the nearest product strategy, and exact realization for general m requires m branches. This resource separation is for the replacement benchmark, not a new coherent-target optimum.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/CompactMatchedReplacementBranchGap.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/WeightedBinaryReplacementExact.replacer_diamond_exact`
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorChannelModel](../FiniteSectorChannelModel.md)
- Dependency: [D5/S3/Quantum/Entanglement/SectorChannels/WeightedBinaryReplacementExact](WeightedBinaryReplacementExact.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../../Foundation/FiniteKrausChannel.md)
