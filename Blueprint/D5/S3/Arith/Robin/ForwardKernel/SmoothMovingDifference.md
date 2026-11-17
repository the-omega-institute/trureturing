# Smooth moving differences

## Abstract

Smooth moving differences on a dyadic interval are controlled by square norms on its enlargement.

**Theorem 1.1 (Three square-norm bounds).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SmoothMovingDifference.smooth_moving_difference_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SmoothMovingDifference.smooth_moving_difference_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an exponent theta strictly between zero and one. There is a positive constant C such that, for all sufficiently large X, all s in [0,1], and every continuously differentiable u on [X/2,4X], the square norm of u(x+s*x^theta)-u(x) on [X,2X] is at most both C*X^theta times the square norm of u' on the enlarged interval and C times that of u. Its derivative has square norm at most C times the enlarged square norm of u'. The constant and threshold are uniform in s and u. The first estimate follows by the fundamental theorem of calculus, Cauchy–Schwarz, and integration over translated intervals. The other two use the expanding change of variable x to x+s*x^theta, whose derivative lies between one and two.

**Theorem 1.2 (Two bounds for endpoint strips).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SmoothMovingDifference.endpoint_strips_integral_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SmoothMovingDifference.endpoint_strips_integral_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For X at least one, exponent a strictly between zero and one, s in [0,1], and [l,r] contained in [X,2X], let J be the union of [l,l+s*l^a] and [r,r+s*r^a]. For every u square integrable on [X/2,4X], the integral of |u| over J is at most 2*sqrt(X^a) times the square norm of u on that enlarged interval. If |u| is also at most a nonnegative U there, the same strip integral is at most 4*X^a*U. The strip measure is at most 4*X^a; the first alternative is Cauchy–Schwarz, and the second integrates the pointwise bound.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SmoothMovingDifference.endpoint_strips_integral_bounds`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SmoothMovingDifference.smooth_moving_difference_bounds`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer](MovingDifferenceTransfer.md)
