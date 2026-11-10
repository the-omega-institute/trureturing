# Identities for dyadic smoothing

## Abstract

Dyadic block identity.

**Theorem 1.1 (Dyadic block identity).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingIdentities.smoothingBlock_eq_averaged_increments`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingIdentities.smoothingBlock_eq_averaged_increments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For R>0, Z_R=A_R(A_R E) and B_R=Z_R-Z_(2R) satisfy B_R=-A_R(A_R D_R E)/2-A_R(A_R D_(2R) E)/4 pointwise. Splitting each window of length 2R into two windows of length R yields this identity.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingIdentities.smoothingBlock_eq_averaged_increments`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity](AveragingRegularity.md)
