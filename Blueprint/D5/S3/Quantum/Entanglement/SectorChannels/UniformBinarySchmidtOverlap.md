# Sharp coherent matched overlap with two labels

## Abstract

Determine the exact worst coherent overlap-to-score ratio for two uniform output labels.

**Theorem 1.1 (Exact two-label optimum and rank-two attainment).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/UniformBinarySchmidtOverlap.actual_binary_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SectorChannels/UniformBinarySchmidtOverlap.actual_binary_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The output score sums the two matching Born probabilities after clipping each at one half. The comparison score sums the minimum of each Schmidt weight and its square root after division by two inside the root.

A direct sum of paired local columns symmetrizes the effects without shared randomness. The Frobenius norms of its four output blocks bound the original leading Schmidt amplitude, giving a two-label cap at arbitrary finite Schmidt rank.

A real two-dimensional rotation gives actual rank-two local columns attaining the bound. The scalar optimum is certified by the root of an explicit polynomial and a rational bracket for the optimum near 1.08487139689.

The conclusion concerns a fixed pure Schmidt resource and independent finite local columns. It is not a statement about input-dependent recovery, diamond distance, or three or more labels.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/UniformBinarySchmidtOverlap.actual_binary_maximum`
- Dependency: [D5/S3/Quantum/Entanglement/SectorChannels/UniformSchmidtOverlap](UniformSchmidtOverlap.md)
