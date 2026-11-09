# Continuous sampling

## Abstract

Continuous sampling transfers short interval moments from integer cells to real points.

**Theorem 1.1 (Pointwise cell discrepancy).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling.sampling_pointwise`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling.sampling_pointwise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an admissible interval inside a fixed window, with integer scale H and M H at most N, the centered Chebyshev increment at x differs from the centered integer-cell sum at floor x by at most 2 log(4N)+2. The two logarithmic terms account for the possible crossings at the left and right endpoints, while the additive constant accounts for the lattice centering count.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling.sampling_pointwise`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FiniteProductMomentBounds](../FourthTransfer/FiniteProductMomentBounds.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ArithmeticTransferDefs](ArithmeticTransferDefs.md)
