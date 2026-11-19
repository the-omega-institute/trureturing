# Conditional interval covariance

## Abstract

A linear square-sum error bound gives a uniform covariance estimate for scaled intervals.

**Definition 1.1 (Overlap length).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IntervalCovariance.overlap`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IntervalCovariance.overlap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The overlap length of the ordered intervals (a,b] and (c,d] is the nonnegative part of min(b,d) minus max(a,c).

**Definition 1.2 (Scaled interval kernel sum).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IntervalCovariance.intervalSum`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IntervalCovariance.intervalSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the kernel over the integer intervals with endpoints given by the natural floors of aH, bH, cH and dH.

**Theorem 1.3 (Uniform interval covariance bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IntervalCovariance.interval_covariance_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IntervalCovariance.interval_covariance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every M at least one and every nonnegative square-sum error constant C₀, there is a nonnegative constant C depending only on M and C₀. For every symmetric translation-invariant kernel whose square prefix sum differs from minus m log m by at most C₀ times m for all positive integers m, the absolute difference between each scaled interval sum and minus H log H times the overlap length is at most C times H, uniformly for H at least one and all ordered endpoints in [0,M], including empty intervals.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IntervalCovariance.intervalSum`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IntervalCovariance.interval_covariance_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IntervalCovariance.overlap`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TranslationInvariantPrefix](TranslationInvariantPrefix.md)
