# Uniform cumulative variance controls the moving-length strip

## Abstract

Uniform cumulative variance controls the moving-length strip.

**Theorem 1.1 (Uniform variance on the length strip).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance.moving_strip_variance_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance.moving_strip_variance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If E is measurable and locally bounded and its cumulative variance has the uniform asymptotic Y u log(Y/u) throughout Y^(3/4)<=u<=Y^(7/8), then eventually every u in [X^(4/5),4X^(4/5)] has increment square integral on [X,2X] at most 32 X X^(4/5) log X. At Y=2X the whole strip eventually lies in the variance band. The cumulative variance bounds the dyadic integral, and log(2X/u)<=2 log X.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance.moving_strip_variance_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance](FixedLengthCovariance.md)
