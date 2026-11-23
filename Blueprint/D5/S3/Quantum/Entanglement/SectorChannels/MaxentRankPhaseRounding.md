# Sharp rounding at a prescribed residual rank phase

## Abstract

The exact rank-count rounding minimum controls the scalar residual packing loss with an optimal factor.

**Theorem 1.1 (Sharp comparison of the rank-count partition and greedy cap packing).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/MaxentRankPhaseRounding.phase_rounding`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SectorChannels/MaxentRankPhaseRounding.phase_rounding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write the rank-scaled weights as integer parts and squared residual caps. If the residual sum is the integer K, rounding up the K largest residuals attains the literal minimum label L1 error among all nonnegative integer counts of the required rank.

The greedy scalar packing error is at most that minimum and at least (K+1)/(2K+1) times it. An additional lower bound becomes asymptotically exact near integer phases. For each positive K an explicit sorted K+3-label profile attains the factor at nonzero distance.

This is the scalar maximally entangled matched-label benchmark. It does not assert the physical channel converse, arbitrary Schmidt spectra, or a solution of coherent RT.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/MaxentRankPhaseRounding.phase_rounding`
