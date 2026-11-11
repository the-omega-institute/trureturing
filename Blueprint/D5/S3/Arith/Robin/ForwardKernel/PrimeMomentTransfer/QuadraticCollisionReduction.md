# Quadratic collision reduction

## Abstract

Quadratic reduction separates distinct-shift products from sparse collision errors.

**Theorem 1.1 (A local error supported on repeated shifts).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCollisionReduction.product_reducedAt_error_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCollisionReduction.product_reducedAt_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be any natural order and T at least one. Suppose the absolute values of the centered von Mangoldt coordinates and of s-2 and s-1 are at most T. The absolute difference between the product of the k coordinates and reducedAt(s,n,d) is at most (8T)^(k-2) times the sum of the absolute quadratic defects over shifts whose multiplicity is at least two. Powers are grouped by their common shift. The reduction coefficients satisfy geometric bounds at every exponent. The scalar error recurrence is the preceding error multiplied by y plus the first reduction coefficient multiplied by the quadratic defect; induction bounds its absolute value by (8T)^(r-2) times that defect for every r at least two. The ordered product expansion then bounds the combined error.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCollisionReduction.product_reducedAt_error_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ArithmeticTransferDefs](ArithmeticTransferDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns](IndexEqualityPatterns.md)
