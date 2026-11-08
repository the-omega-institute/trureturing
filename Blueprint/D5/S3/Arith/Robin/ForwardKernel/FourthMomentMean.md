# Vanishing normalized first moment

## Abstract

Short averages control the first moment of a moving price-weighted profile.

Let E be locally bounded and measurable, and assume the cumulative variance asymptotic uniformly in an exponent band 0<alpha<theta<beta<1. Fix theta<nu<beta, put M=X^nu, and let g be a real integrable profile on (0,1).

**Theorem 1.1 (Uniform moving-increment primitives).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentMean.moving_primitive_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthMomentMean.moving_primitive_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be locally bounded and measurable. Assume its cumulative variance asymptotic in a band 0<alpha<theta<beta<1 and choose theta<nu<beta. There is C>0 such that for all sufficiently large X, every s in [0,1] and every y in [X,2X], the absolute integral from X to y of E(x+s*x^theta)-E(x) is at most C*sqrt(log X) times (X^(1+theta-nu/2)+X^((1+theta+nu)/2)).

**Theorem 1.2 (Quantitative first-moment bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentMean.profile_response_mean_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthMomentMean.profile_response_mean_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a constant C>0 such that, for all sufficiently large X, the absolute value of the integral of profileResponse(E,theta,g,x)/x over [X,2X] is at most C times the L1 norm of g times sqrt(log X) times (X^((1-nu)/2)+X^((nu-theta)/2)).

For f_s(x)=E(x+s*x^theta)-E(x), the short-average estimate and the moving-increment square bound on [X,3X] give a uniform primitive bound sqrt(log X) times (X^(1+theta-nu/2)+X^((1+theta+nu)/2)). The endpoint-strip comparison is the constant-second-function case of FourScaleCovariance.covariance_of_norm_bounds. For the price weight use ProfileCrossIntegral.crossWeight with exponents theta and 1/2 and second parameter zero. Its existing smoothness and variation estimate give total variation including the right endpoint at most (27+theta+1/2)*X^(-theta-1/2). WeightedPrimitiveBound.weighted_integral_le_of_primitive_bound then gives the bound for each s. Local boundedness of E and integrability of g justify Fubini and the final L1 estimate.

**Theorem 1.3 (The normalized mean tends to zero).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentMean.profile_response_mean_tendsto_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthMomentMean.profile_response_mean_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral of profileResponse(E,theta,g,x)/x over [X,2X], divided by sqrt(X^(1-theta)*log X), tends to zero as X tends to infinity. Dividing the quantitative bound by this square root leaves a constant times X^(-(nu-theta)/2)+X^(-(1-nu)/2), and both terms tend to zero. The statement concerns the normalized first moment.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentMean.moving_primitive_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentMean.profile_response_mean_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentMean.profile_response_mean_tendsto_zero`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourScaleCovariance](FourScaleCovariance.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/ProfileCrossIntegral](ProfileCrossIntegral.md)
