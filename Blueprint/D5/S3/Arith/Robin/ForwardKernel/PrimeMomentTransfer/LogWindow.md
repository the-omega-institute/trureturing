# Logarithmic dyadic window

## Abstract

Uniform logarithmic variance and interval overlap bounds.

**Theorem 1.1 (Variation of the squared logarithmic ratio).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/LogWindow.log_square_error`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/LogWindow.log_square_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N at least two, one at most H at most N, and x in [N,2N], the squared ratio log(x/H)/log N differs from the squared ratio log(N/H)/log N by at most 3 log 2 divided by log N.

**Theorem 1.2 (Bounds for the logarithmic variance ratio).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/LogWindow.variance_ratio_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/LogWindow.variance_ratio_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N at least two and one at most H at most N, the ratio log(N/H)/log N lies between zero and one.

**Theorem 1.3 (Bounds for the fourth overlap pairing).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/LogWindow.w4_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/LogWindow.w4_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For four ordered intervals in [0,M] with nonnegative M, the sum of the three products of overlap lengths lies between zero and 3 M squared.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/LogWindow.log_square_error`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/LogWindow.variance_ratio_bounds`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/LogWindow.w4_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds](FormalIntervalMomentBounds.md)
