# Uniform single-length rates

## Abstract

Explicit errors in single-length prime moments decay uniformly on polynomial length bands.

**Definition 1.1 (Cumulative sampling rate).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates.cumulativeSamplingRate`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates.cumulativeSamplingRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The relative cumulative sampling envelope is sqrt(log Y/v) plus (log Y/v)^(k/2) plus (v log Y)^(k/2)/Y. The last summand bounds the terminal fractional cell.

**Theorem 1.2 (Uniform moment error).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates.ms_error_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates.ms_error_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For moment order two or four and positive alpha less than beta less than one quarter, the full explicit Montgomery–Soundararajan error is little-o of Y v^(k/2) log(Y/v)^(k/2) uniformly on the polynomial band, provided epsilon is positive and less than one half minus twice beta.

**Theorem 1.3 (Uniform sampling envelope).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates.sampling_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates.sampling_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For moment order two or four and positive alpha less than beta less than one quarter, the sum of sqrt(log Y/v), (log Y/v)^(k/2), and (v log Y)^(k/2)/Y tends to zero uniformly for Y^alpha at most v at most Y^beta.

**Theorem 1.4 (Uniform rounding error in the main term).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates.main_errors_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates.main_errors_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For moment order two or four and positive alpha less than beta less than one quarter, replacing the cutoff and length by their natural floors changes the main term by little-o of Y v^(k/2) log(Y/v)^(k/2), uniformly on the polynomial band.

**Theorem 1.5 (Normalized second main term).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates.second_main_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates.second_main_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive alpha less than beta less than one, the second main term divided by Y v log(Y/v) tends to one uniformly for Y^alpha at most v at most Y^beta. The exact logarithmic integral leaves a remainder bounded by a constant times Y, and log(Y/v) is at least (1-beta) log Y.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates.cumulativeSamplingRate`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates.main_errors_uniform`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates.ms_error_uniform`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates.sampling_uniform`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates.second_main_uniform`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthBandGeometry](SingleLengthBandGeometry.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms](SingleLengthMainTerms.md)
