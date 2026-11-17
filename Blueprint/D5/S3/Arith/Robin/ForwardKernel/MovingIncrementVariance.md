# MovingIncrementVariance

## Abstract

Averaging comparable increments gives a bound uniform over moving increment parameters.

**Theorem 1.1 (Uniform moving-increment bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingIncrementVariance.moving_increment_square_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingIncrementVariance.moving_increment_square_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be Borel measurable and locally bounded, and assume the cumulative variance asymptotic uniformly in the band Y^alpha<=u<=Y^beta, where 0<alpha<theta<beta<1. There is C>0 and one threshold for X such that every s in [0,1] satisfies integral_X^(2X) D_(s*x^theta)(x)^2 dx<=C*X*X^theta*log(X). Apply the two-endpoint square estimate with p(x)=x, q(x)=x+s*x^theta, R=X^theta, C0=2, m=1, and Y=3X. The comparable-length variance estimate supplies a common bound for R<=u<=4R. The moving endpoint has derivative 1+s*theta*x^(theta-1)>=1; its gap is at most 2R and its image lies in [1,3X]. The estimate applies to measurable locally bounded E. All length and image bounds hold at one threshold independently of s.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingIncrementVariance.moving_increment_square_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance](MovingLengthVariance.md)
