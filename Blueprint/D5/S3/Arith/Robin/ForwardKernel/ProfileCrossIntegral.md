# From covariance to profile cross integrals

## Abstract

Uniform bounds for moving-increment primitives control cross integrals of weighted profiles.

**Definition 1.1 (Weight for a pair of moving profiles).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/ProfileCrossIntegral.crossWeight`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/ProfileCrossIntegral.crossWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a,b,s,t,x, define the cross weight as x^(-a-b)*priceRatio(x,s*x^a)*priceRatio(x,t*x^b).

**Theorem 1.2 (Continuous differentiability of the cross weight).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/ProfileCrossIntegral.crossWeight_contDiffOn`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/ProfileCrossIntegral.crossWeight_contDiffOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For X>=4 and s,t>=0, the cross weight is continuously differentiable on [X,2X], for arbitrary real a and b. The displaced arguments remain above one, where the price weight is smooth and positive.

**Theorem 1.3 (Endpoint and variation bound for the cross weight).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/ProfileCrossIntegral.crossWeight_variation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/ProfileCrossIntegral.crossWeight_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If 0<a,b<1, X>=4, and s,t belong to [0,1], then the absolute value of the cross weight at 2X plus the integral of its absolute derivative from X to 2X is at most (27+a+b)*X^(-a-b).

**Theorem 1.4 (Uniform profile estimate).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/ProfileCrossIntegral.profile_cross_integral_of_covariance_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/ProfileCrossIntegral.profile_cross_integral_of_covariance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be measurable and bounded on every compact interval, let 0<a,b<1, and let B be any nonnegative function. Suppose a constant C0 bounds the absolute integral from X to y of (E(x+s*x^a)-E(x))*(E(x+t*x^b)-E(x)) by C0*B(X), uniformly for s,t in [0,1] and y in [X,2X], for all sufficiently large X. Then a positive constant C bounds the absolute integral over [X,2X] of profileResponse(E,a,g1,x)*profileResponse(E,b,g2,x)/x by C*profileL1(g1)*profileL1(g2)*X^(-a-b)*B(X). Both C and the threshold are independent of the integrable profiles.

The exact normalized response formula expresses the cross integral as an integral over the two profile parameters of weighted covariance. On each fixed compact spatial interval, local boundedness of E dominates the joint integrand by a constant times |g1(s)*g2(t)|, which justifies Fubini. The weight is W(x)=x^(-a-b)*priceRatio(x,s*x^a)*priceRatio(x,t*x^b). The price-ratio derivative bound gives |W(2X)|+integral_X^(2X)|W'(x)| dx <= (27+a+b)*X^(-a-b). Integration by parts for the absolutely continuous covariance primitive then gives the stated estimate after integration against |g1(s)*g2(t)|.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/ProfileCrossIntegral.crossWeight`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/ProfileCrossIntegral.crossWeight_contDiffOn`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/ProfileCrossIntegral.crossWeight_variation`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/ProfileCrossIntegral.profile_cross_integral_of_covariance_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs](CrossExponentDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/ProfileKernelDefs](ProfileKernelDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/WeightControl](WeightControl.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/WeightRemoval](WeightRemoval.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/WeightedPrimitiveBound](WeightedPrimitiveBound.md)
