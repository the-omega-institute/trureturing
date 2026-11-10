# Transfer of moving differences

## Abstract

An expanding moving substitution transfers a difference onto a smooth test function and two endpoint strips.

**Definition 1.1 (Endpoint strips).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.endpointStrips`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.endpointStrips` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a moving shift with exponent theta and profile parameter s, endpointStrips(theta,s,l,r) is the union of the intervals from l to its shifted endpoint and from r to its shifted endpoint.

**Theorem 1.2 (Square integrals under an expanding map).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.square_comp_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.square_comp_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a differentiable map on [l,r] has derivative at least one and maps into [L,R], the square integral of a measurable square-integrable function composed with that map is at most its square integral on [L,R]. The composed square is integrable. The change of variables formula and the positive derivative lower bound give the result.

**Theorem 1.3 (Nonnegative displacement).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.moving_shift_nonneg_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.moving_shift_nonneg_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive exponent theta, a nonnegative x, and s in [0,1], the moving point x+s*x^theta lies to the right of x.

**Theorem 1.4 (Uniform displacement on a dyadic interval).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.moving_shift_gap_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.moving_shift_gap_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If 0<theta<1, X>=1, x is in [X,2X], and s is in [0,1], the displacement s*x^theta is at most 2*X^theta.

**Theorem 1.5 (The endpoint strips lie in the working interval).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.endpointStrips_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.endpointStrips_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<theta<1, X>=1, s in [0,1], and X<=l<=r<=2X, both endpoint strips lie in [X/2,4X]. The displacement bound and X^theta<=X give the upper endpoint bound.

**Theorem 1.6 (Square norm of a sliding primitive).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.sliding_primitive_l2_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.sliding_primitive_l2_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let u be measurable and square integrable on [L,R]. Suppose [l,r] lies inside [L,R], phi is continuous, and 0<=phi(x)-x<=H on [l,r], with phi(x)<=R. The square norm of the integral of u from x to phi(x), viewed as a function of x in [l,r], is at most H times the square norm of u on [L,R]. Cauchy–Schwarz bounds each moving interval integral; after interchanging the integrals, each point belongs to a set of starting points of length at most H.

**Theorem 1.7 (Transfer onto a smooth test function).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.moving_difference_transfer_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.moving_difference_transfer_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix 0<a<1. There is C>0 such that, for all sufficiently large X, uniformly for s in [0,1] and [l,r] contained in [X,2X], the absolute integral of (u(x+s*x^a)-u(x))*v(x) is at most C times the sum of X^a*||u||2*||v'||2, (X^a/X)*||u||2*||v||2, and V times the integral of |u| over the union of [l,l+s*l^a] and [r,r+s*r^a]. Here u is measurable and square integrable on [X/2,4X], v is continuously differentiable there, |v|<=V, and all square norms are on that enlarged interval. The proof uses the sliding primitive of u, forward change of variables, and integration by parts for absolutely continuous primitives.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.endpointStrips`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.endpointStrips_subset`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.moving_difference_transfer_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.moving_shift_gap_le`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.moving_shift_nonneg_gap`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.sliding_primitive_l2_le`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.square_comp_le`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs](CrossExponentDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingEndpointVariance](MovingEndpointVariance.md)
