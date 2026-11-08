# MovingLengthVariance

## Abstract

Uniform band variance controls comparable, common-band, and shorter increment lengths.

**Theorem 1.1 (Comparable increment lengths).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance.comparable_length_variance_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance.comparable_length_variance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume E is locally bounded and Borel measurable, and its cumulative variance is asymptotic to Y*u*log(Y/u) uniformly for Y^alpha<=u<=Y^beta, where 0<alpha<theta<beta<1. For fixed 0<A<=B and d>0 there is C>0 such that, for all sufficiently large X and all A*X^theta<=u<=B*X^theta, V(d*X,u)<=C*X*X^theta*log(X). Under these hypotheses, both ends of this entire length interval enter the exponent band at one threshold.

**Theorem 1.2 (All shorter increments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance.shorter_increment_square_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance.shorter_increment_square_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume E is locally bounded and Borel measurable, and its cumulative variance is asymptotic to Y*u*log(Y/u) uniformly for Y^alpha<=u<=Y^beta, where 0<alpha<theta<beta<1. Under these hypotheses, for every c>0 there is C>0 such that, for all sufficiently large X and every 0<=u<=h=c*X^theta, the integral of D_u(x)^2 over [X,2X] is at most C*X*h*log(X/h). Apply the two-endpoint square estimate with p(x)=x, q(x)=x+u, R=h, C0=1, and m=1. The comparable-length estimate controls V(3X,v) uniformly for h<=v<=3h, and log(X/h)=(1-theta)*log(X)-log(c).

**Theorem 1.3 (Variance on a common power band).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance.band_range_variance_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance.band_range_variance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume E is locally bounded and Borel measurable, 0<alpha<a<b<beta<1, and its cumulative variance V(Y,u) is asymptotic to Y*u*log(Y/u) uniformly for Y^alpha<=u<=Y^beta. For every fixed d>0, the cumulative variance at d*X is bounded uniformly for every length between X^a and 8*X^b by a constant times X*u*log(X). Under these hypotheses, the endpoints are placed inside the original asymptotic band at one threshold, and the asymptotic estimate is converted using u>=1.

**Theorem 1.4 (Uniform increment norm on a common band).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance.band_increment_square_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance.band_increment_square_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume E is locally bounded and Borel measurable, 0<alpha<a<b<beta<1, and its cumulative variance V(Y,u) is asymptotic to Y*u*log(Y/u) uniformly for Y^alpha<=u<=Y^beta. Under these hypotheses, for all sufficiently large X and every 0<=u<=8*X^b, the square integral of the increment of E over [X/2,4X] is bounded by a constant times X*max(u,X^a)*log(X). The short range u<=X^a uses the two-endpoint estimate with comparison length X^a, while the long range uses comparison length u/2 and the common-band variance bound.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance.band_increment_square_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance.band_range_variance_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance.comparable_length_variance_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance.shorter_increment_square_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance](FixedLengthCovariance.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingEndpointVariance](MovingEndpointVariance.md)
