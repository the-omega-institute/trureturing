# Bounds and pairing for forward averages

## Abstract

Forward window averages commute with integrable pairings.

**Theorem 1.1 (Pairing and translation averages).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/AveragingBounds.windowAverage_pairing_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/AveragingBounds.windowAverage_pairing_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For M>=0 and l<=r, assume that f(x+t)*z(x) is integrable on the product of (l,r] and (0,M]. The integral of the M-window average of f times z on [l,r] equals 1/M times the integral over t in [0,M] of the integral of f(x+t)*z(x) over x in [l,r]. This also holds for zero window length and degenerate spatial intervals.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/AveragingBounds.windowAverage_pairing_eq`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs](CrossExponentDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer](VarianceTransfer.md)
