# Shared Schatten continuity

## Abstract

The existing actual Schatten trace and continuity proofs are shared by the finite power supplier and the original strict spectral consumer.

**Theorem 1.1 (Actual column Gram trace).**

Lean statement: `D5/S3/Quantum/NormCompression/SchattenContinuity.schattenPow_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/SchattenContinuity.schattenPow_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural square dimension, including zero, and every positive real p, the actual singular value power sum equals the real trace of the p/2-th functional calculus power of A* A. This exact proof was extracted from StrictSpectralPolyaRefutation and is reused without reproving it.

**Theorem 1.2 (Continuity of actual Schatten powers).**

Lean statement: `D5/S3/Quantum/NormCompression/SchattenContinuity.continuous_schattenPow`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/SchattenContinuity.continuous_schattenPow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real exponent the actual Schatten power is continuous on square complex matrices, including the zero dimension. The original strict spectral consumer and the finite power trace supplier both import this existing proof. The extraction adds no new continuity assertion or literature novelty claim.

## References

- Truth anchor: `D5/S3/Quantum/NormCompression/SchattenContinuity.continuous_schattenPow`
- Truth anchor: `D5/S3/Quantum/NormCompression/SchattenContinuity.schattenPow_trace`
- Dependency: [D5/S3/Quantum/NormCompression/UpperBranchReduction](UpperBranchReduction.md)
- Dependency: [D5/S3/Resource/LogDet/PathSpectralClassical](../../Resource/LogDet/PathSpectralClassical.md)
