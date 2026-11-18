# Local factor comparison

## Abstract

Finite arithmetic bounds for exception counting.

**Theorem 1.1 (Local factor upper bound).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionLocal.local_factor_upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionLocal.local_factor_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For kappa at least one, reciprocal r between zero and one half, and exponent a at least one, the normalized local factor is at most (1-r)^(-kappa)(1-r^kappa). Convexity compares equal-length increments of the real power function.

**Theorem 1.2 (Monotone endpoint).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionLocal.endpoint_monotone`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionLocal.endpoint_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For kappa at least one, the endpoint (1-r)^(-kappa)(1-r^kappa) is nondecreasing with r on [0,1). Writing r/(1-r) as a new coordinate reduces this to monotonicity of unit increments of a convex real power.

**Theorem 1.3 (Finite support replacement).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionLocal.support_product_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionLocal.support_product_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A support S of smaller cardinality has no larger product when f(p) is nonnegative for every p in S, every displaced factor is below a boundary value B and every replacement factor is above B, with B at least one. The proof retains the common support and compares the two remaining products through powers of B.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionLocal.endpoint_monotone`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionLocal.local_factor_upper_bound`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionLocal.support_product_le`
- Dependency: [D5/S3/Arith/Robin/Analytic/LcmPowerLocalFactorBound](../LcmPowerLocalFactorBound.md)
