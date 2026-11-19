# Trace coordinates for five-site periodic binary bond-two states

## Abstract

Trace coordinates for five-site periodic binary bond-two states

**Theorem 1.1 (Homogeneous necklace amplitudes).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCoordinates.trace_word_necklaces`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCoordinates.trace_word_necklaces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The eight cyclic amplitudes are weighted degree-five polynomials in the two traces, two determinants and mixed trace.

**Theorem 1.2 (The physical Gram matrix).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCoordinates.flatten_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCoordinates.flatten_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cyclicity identifies the actual adjacent two-site marginal with the Hermitian Gram matrix of the necklace flattening.

**Theorem 1.3 (Realization of every trace tuple).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCoordinates.exists_trace_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCoordinates.exists_trace_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A companion matrix and an upper triangular matrix realize the invariants using one complex quadratic root.

**Theorem 1.4 (Reconstruction on the trace-aligned chart).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCoordinates.aligned_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCoordinates.aligned_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After division by the trace factor, three amplitude ratios recover the three projective source ratios.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCoordinates.aligned_inverse`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCoordinates.exists_trace_coordinates`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCoordinates.flatten_gram`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCoordinates.trace_word_necklaces`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteAmbiguity](PeriodicMPSTwoSiteAmbiguity.md)
