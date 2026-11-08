# Real length rescaling

## Abstract

Exact rescaling passes from real interval lengths to their natural floors.

**Theorem 1.1 (Exact mixed-moment rescaling).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling.moment_rescale`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling.moment_rescale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive N, H and K with positive log N, rescaling every endpoint by H/K leaves the physical increments unchanged. The normalized moment acquires the factor (K/H)^(k/2).

**Theorem 1.2 (Scaling overlap pairings).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling.w4_rescale`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling.w4_rescale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication of all endpoints by a nonnegative real r multiplies each overlap length by r and the sum of paired overlap products by r squared.

**Theorem 1.3 (Rescaled endpoint window).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling.rescaled_admissible`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling.rescaled_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An admissible family in the window M remains admissible in the window 2M after multiplication of its endpoints by a factor between zero and two.

**Theorem 1.4 (Floor length in the polynomial band).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling.floor_range`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling.floor_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<alpha<beta<1 and sufficiently large N, every H between N^alpha and N^beta has positive natural floor K, with N^(alpha/2)<=K<=N^beta and 1<=H/K<=2.

**Theorem 1.5 (Uniform floor variance error).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling.floor_variance_rate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling.floor_variance_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<alpha<beta<1, the difference between the squared logarithmic variance ratios at H and its natural floor tends uniformly to zero over N^alpha<=H<=N^beta.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling.floor_range`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling.floor_variance_rate`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling.moment_rescale`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling.rescaled_admissible`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling.w4_rescale`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/LogWindow](LogWindow.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates](UniformRates.md)
