# Continuous sampling

## Abstract

Continuous sampling transfers short interval moments from integer cells to real points.

**Theorem 1.1 (Floor shift cases add nat).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling.floor_shift_cases_add_nat`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling.floor_shift_cases_add_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural n, 0<=x<1 and A>=0, floor(n+x+A) is either n+floor A or n+floor A+1.

**Theorem 1.2 (Psi endpoint discrepancy).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling.psi_endpoint_discrepancy`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling.psi_endpoint_discrepancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two ordered positive integer endpoints are each shifted by zero or one and the shifted endpoints are at most 4L with L>=1, the change in their Chebyshev psi difference is at most 2 log(4L) in absolute value.

**Theorem 1.3 (S eq psi shift).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling.S_eq_psi_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling.S_eq_psi_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H>=0 and 0<=a<=b, the centered interval sum S(H,a,b,n) equals the difference of psi at n+floor(bH) and n+floor(aH), minus floor(bH)-floor(aH).

**Theorem 1.4 (Pointwise cell discrepancy).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling.sampling_pointwise`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling.sampling_pointwise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an admissible interval inside a fixed window, with integer scale H and M H at most N, the centered Chebyshev increment at x differs from the centered integer-cell sum at floor x by at most 2 log(4N)+2. The two logarithmic terms account for the possible crossings at the left and right endpoints, while the additive constant accounts for the lattice centering count.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling.S_eq_psi_shift`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling.floor_shift_cases_add_nat`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling.psi_endpoint_discrepancy`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling.sampling_pointwise`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FiniteProductMomentBounds](../FourthTransfer/FiniteProductMomentBounds.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ArithmeticTransferDefs](ArithmeticTransferDefs.md)
