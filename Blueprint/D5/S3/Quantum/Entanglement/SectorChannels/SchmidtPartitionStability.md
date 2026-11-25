# A quantitative inverse bound for labeled Schmidt partitions

## Abstract

Sorted spectral caps certify a quantitative distance to exact Schmidt partitions.

**Theorem 1.1 (Exact finite partition distance from sorted spectral data).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/SchmidtPartitionStability.sorted_partition_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SectorChannels/SchmidtPartitionStability.sorted_partition_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The readout is the minimum absolute label-weight error over all finite assignments of the squared Schmidt amplitudes. It uses arbitrary normalized label weights, any finite positive label count, and allows padded zero amplitudes.

From sorted nonnegative spectral amplitudes, prefix majorization and the cap-overlap inequality, Abel summation bounds the cross correlation. Cauchy-Schwarz on the squared difference then controls the actual grouped Schmidt error. Eliminating the unobserved spectral mass deficit produces the small-error inverse curve, the large-error linear bound, and the spacing gap 2/[T(T+1)].

This theorem consumes scalar spectral premises. It does not formalize the channel-to-Gram implication, the Schur-Horn frame converse, Fourier optimality, computational complexity, or the original coherent RT problem.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/SchmidtPartitionStability.sorted_partition_inverse`
