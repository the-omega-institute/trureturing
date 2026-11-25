# Rectangular spectra and projection frames

## Abstract

Rectangular spectra and projection frames

**Theorem 1.1 (Spectral sums of rectangular products).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/ProjectionSpectralTransport.spectralSum_mul_reverse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/ProjectionSpectralTransport.spectralSum_mul_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A and B be rectangular complex matrices with Hermitian products AB and BA. Summing any real function that vanishes at zero over the two spectra gives the same value. The rectangular characteristic polynomial identity accounts for the extra zero roots.

**Theorem 1.2 (An isometric frame of the prescribed rank).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/ProjectionSpectralTransport.exists_projection_frame`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/ProjectionSpectralTransport.exists_projection_frame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every Hermitian idempotent Q of rank d is VV† for a matrix V with d columns and V†V = I. The zero and identity projections give the empty and reindexed identity frames. A complementary frame supplies the intermediate case.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/Auric/ProjectionSpectralTransport.exists_projection_frame`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/ProjectionSpectralTransport.spectralSum_mul_reverse`
- Dependency: [D5/S3/Quantum/Measurement/Auric/ProjectionFrames](ProjectionFrames.md)
