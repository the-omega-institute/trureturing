# Kuperberg bounds for smoothed intervals

## Abstract

Kuperberg bounds for smoothed intervals.

**Theorem 1.1 (Kuperberg bounds for smoothed intervals).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveKuperbergBridge.kuperberg_raw_implies_smoothed`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveKuperbergBridge.kuperberg_raw_implies_smoothed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume KuperbergRaw, the real-weight third- and fourth-order specialization of Kuperberg, arXiv:2301.06095v1, Theorem 1.3. Every fixed shifted smoothed interval with positive smoothing parameter and nonnegative ordered endpoints belongs to the smooth positive-support weight class and has quadratic Fourier decay, by smooth_interval_admissible. The weighted moment identity converts the raw third moment and each of the three bilinear fourth-moment pairings into the finite-sieve expectation coordinates. Complex norms of real casts equal absolute values, so the same nonnegative constants give KuperbergSmoothed, uniformly in squarefree Q and natural h at least three, with exactly the stated density powers and error exponents.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveKuperbergBridge.kuperberg_raw_implies_smoothed`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFourierAdmissibility](SieveFourierAdmissibility.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothMomentBridge](SieveSmoothMomentBridge.md)
