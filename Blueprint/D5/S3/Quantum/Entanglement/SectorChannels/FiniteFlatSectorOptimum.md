# Compact Flat Sector Optimum

## Abstract

Compact flat bipartite sector encodings admit a simultaneous optimal local splitting channel, with error determined by the distinct logarithms of the residual ranks.

**Theorem 1.1 (The exact optimum on the compact physical carriers).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/FiniteFlatSectorOptimum.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SectorChannels/FiniteFlatSectorOptimum.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sectors form any nonempty finite set. Source and target ranks are arbitrary positive integers in each sector. A flat bipartite source can produce the exact flat target on every logical basis sector by local completely positive trace-preserving maps exactly when each source rank is the target rank times a positive integer residual rank.

For feasible ranks, split a local source coordinate into a target coordinate a and a residual coordinate b using the little-endian index a plus the target rank times b. Embed each residual space in one common finite environment by its initial segment. The resulting placement matrix is an isometry. Its tensor square intertwines the complete coherent source encoding with the padded encoding on every logical matrix, including the coherences between different sectors.

The embedding induces an actual quantum channel. A completely positive trace-preserving retraction inverts it on its image and resets the unused orthogonal complement to a fixed state. Tensoring these channels gives physical realizations on all matrices. Restriction and extension through this pair identify both sets of errors of arbitrary product channels on the compact and padded carriers.

Use the same splitting on both sides and discard the residual coordinate. Its local action is the partial trace of the placed physical input matrix. The joint output on a logical matrix is the target encoding of its Schur product with the residual Gram kernel. Each Gram entry is the square root of the smaller residual rank divided by the larger, equivalently the exponential of minus one half of the absolute difference of their logarithms. Every logical basis sector has exactly the target pure output.

Order the distinct residual ranks increasingly and let the loss labels be their logarithms. The sector-to-label map is surjective, and recovers each original residual rank. Summing probabilities over its fibers preserves the kernel energy. A section lifts every probability vector on the distinct labels, so repetitions do not alter the minimum. The exponential kernel equilibrium has minimum energy equal to the reciprocal of one plus T, where T sums the hyperbolic tangents of one quarter of each consecutive loss gap.

The finite sector channel optimum and the exponential kernel minimum therefore give unhalved diamond error two T divided by one plus T. The diamond distance includes every finite passive reference and every joint density input. The splitting product attains this value, which is a least element of the error set for all local product channels and also of the set constrained to exact target outputs on all basis sectors. Consequently the same value is the infimum of the latter set.

If there is only one distinct residual rank, the gap sum is empty and the error is zero. In particular, this includes a single logical sector and any number of sectors with a common residual rank. The construction uses local quantum channels and a discarded environment, with no communication, postselection or additional shared entanglement.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/FiniteFlatSectorOptimum.result`
- Dependency: [D5/S3/Quantum/Entanglement/ExponentialSectorKernel](../ExponentialSectorKernel.md)
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorChannelOptimality](../FiniteSectorChannelOptimality.md)
- Dependency: [D5/S3/Quantum/Reduction/CoherentFlagPort](../../Reduction/CoherentFlagPort.md)
