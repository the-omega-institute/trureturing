# Support and mass of the smoothing kernel

## Abstract

Support and mass of the smoothing kernel

**Theorem 1.1 (Exact kernel support).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothKernel.smoothing_kernel_support`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothKernel.smoothing_kernel_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive delta, the topological support of smoothingKernel is the closed interval [delta,3 delta], and its nonzero set is the open interval (delta,3 delta).

**Theorem 1.2 (Nonnegative unit mass).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothKernel.smoothing_kernel_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothKernel.smoothing_kernel_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive delta, smoothingKernel is nonnegative at every real point and its integral over the real line is one.

**Theorem 1.3 (Compact shifted support).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothKernel.smooth_interval_support`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothKernel.smooth_interval_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For zero at most a at most b and positive delta, the smoothed interval indicator has compact support contained in [a+delta,b+3 delta]. This includes the empty interval a=b.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothKernel.smooth_interval_support`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothKernel.smoothing_kernel_mass`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothKernel.smoothing_kernel_support`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs](SieveAnalyticDefs.md)
