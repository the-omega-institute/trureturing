# Quadratic collision reduction

## Abstract

Quadratic reduction separates distinct-shift products from sparse collision errors.

**Theorem 1.1 (A local error supported on repeated shifts).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCollisionReduction.product_reducedAt_error_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCollisionReduction.product_reducedAt_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be at most four and T at least one. Suppose the absolute values of the centered von Mangoldt coordinates and of s-2 and s-1 are at most T. The absolute difference between the product of the k coordinates and reducedAt(s,n,d) is at most (8T)^(k-2) times the sum of the absolute quadratic defects over shifts whose multiplicity is at least two. Powers are grouped by their common shift. The scalar errors in exponents two, three, and four are the quadratic defect multiplied respectively by 1, y+s-2, and y squared+(s-2)y+(s-2) squared+s-1. The ordered product expansion then bounds the combined error.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCollisionReduction.product_reducedAt_error_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ArithmeticTransferDefs](ArithmeticTransferDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns](IndexEqualityPatterns.md)
