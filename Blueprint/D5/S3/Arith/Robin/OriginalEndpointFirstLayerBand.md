# Original endpoint first-layer bands

## Abstract

First-layer prime bands and quantitative lower bounds for the complete original endpoint tail.

For each real q>0, retain either original endpoint N=strictInteger(q) or N=maximalInteger(q). Write u=largestPrime(N), a_p=N.factorization(p), m(p,k)=goldenLayerMarginal(p,k), and T=tail(N)=sum over every p in N.primeFactors of -log(1-p^(-(a_p+1))). The integer, complete support, higher layers and all simultaneous activation ties are retained. Every lower bound below concerns this same complete T.

**Theorem 1.1 (The endpoint's own omitted prime bounds its price).**

Lean statement: `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_price_lower_of_largest`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_price_lower_of_largest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either actual endpoint, q>0 and u>=2 imply 1/((2u+1)log(2u))<=q. Bertrand supplies a prime v with u<v<=2u, so v is absent from this endpoint and its omitted first layer satisfies m(v,1)<=q. The existing lower logarithm estimate gives m(v,1)>=1/((v+1)log(v)); positive-factor monotonicity pays the displayed bound. No price cutoff is assumed.

**Theorem 1.2 (Every prime from twice the square root to the largest prime has one layer).**

Lean statement: `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_first_layer_band`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_first_layer_band` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For q>0, either original endpoint, u>=2 and every prime p with 2sqrt(u)<=p<=u, the theorem gives p in N.primeFactors and a_p=1. The actual endpoint classifiers and first-layer prime antitonicity supply the support inclusion. The omitted-prime price bound and the existing second-marginal estimate give m(p,2)<=1/(p^2 log(p))<q. The denominator gap is strict even at p=2sqrt(u), so the second layer is excluded under both strict and maximal tie conventions.

**Theorem 1.3 (A Bertrand witness gives a strict lower bound for the complete tail).**

Lean statement: `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_tail_gt_inv_sixteen_mul_largest`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_tail_gt_inv_sixteen_mul_largest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either actual endpoint at every q>0, u>=16 implies T>1/(16u). Bertrand applied at floor(2sqrt(u)) supplies a prime with 2sqrt(u)<p<=4sqrt(u)<=u. Its actual exponent is one, hence its tail is -log(1-p^-2)>p^-2>=1/(16u). Every other prime and layer stays in T with a nonnegative contribution; the witness does not replace the original support.

**Theorem 1.4 (The complete tail controls the actual theta mass of a first-layer band).**

Lean statement: `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_tail_ge_theta_band`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_tail_ge_theta_band` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For q>0, either original endpoint and u>=2, every real band 2sqrt(u)<=A<=B<=u satisfies T>=(theta(B)-theta(A))/(B^2 log(B)). The exact theta difference is the sum of log(p) over all actual primes A<p<=B. Every such prime has exponent one, and its tail is at least log(p)/(B^2 log(B)). The complete complementary tail remains nonnegative. An empty band is allowed; no prime-density or final-sign premise is supplied.

**Theorem 1.5 (Existing Chebyshev estimates supply an explicit bound from u>=64).**

Lean statement: `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_tail_ge_chebyshev`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_tail_ge_chebyshev` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put s=sqrt(u) and E(u)=(4s-1)log(2)-log(8s+2)-2sqrt(8s)log(8s). For either original endpoint at every q>0, u>=64 implies T>=max(0,E(u))/(64u log(8sqrt(u))). The threshold ensures (2sqrt(u),8sqrt(u)] lies inside the actual first-layer support band. The existing Chebyshev lower bound at 8sqrt(u), upper bound at 2sqrt(u), and theta monotonicity pay the numerator. The maximum with zero does not assume that the explicit expression is positive at small u.

**Theorem 1.6 (A positive lower bound on the square-root logarithmic scale).**

Lean statement: `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_tail_ge_sqrt_log`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_tail_ge_sqrt_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either original endpoint at every q>0, u>=2^22 implies T>=log(2)/(32sqrt(u)log(8sqrt(u))). The constants are paid by proving E(u)>=2sqrt(u)log(2), using only elementary logarithm bounds and square-root identities. This consumes the preceding explicit Chebyshev bound and supplies the positive 1/(sqrt(u)log(u)) scale for this same integer's complete Euler tail.

The original residual remains margin(N)=E3(u)+T+log(log(log(N)))-log(log(u)). A positive quantitative lower bound for T does not establish the joint sign of these terms. The full all-price original Robin endpoint sign and the corresponding RH conclusion remain unpaid; none is a premise or a conclusion of the tail estimates.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_first_layer_band`
- Truth anchor: `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_price_lower_of_largest`
- Truth anchor: `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_tail_ge_chebyshev`
- Truth anchor: `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_tail_ge_sqrt_log`
- Truth anchor: `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_tail_ge_theta_band`
- Truth anchor: `D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.endpoint_tail_gt_inv_sixteen_mul_largest`
- Dependency: [D5/S3/Arith/GoldenLayerMarginalDecay](../GoldenLayerMarginalDecay.md)
- Dependency: [D5/S3/Arith/Robin/OriginalEndpointPrimeTail](OriginalEndpointPrimeTail.md)
