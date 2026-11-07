# Removing the price weight from profiles

## Abstract

Price removal for integrable moving profiles has a negligible mean-square error.

Let E be locally bounded and Borel measurable, let g be an integrable Borel profile on (0,1), and put H(x)=x^theta. The unweighted response is sqrt(x)*P(H(x),g,x), where P is the profile average. The weighted response inserts rho(x,u)=w(x+u)/w(x) into the defining integral.

**Theorem 1.1 (Local square integrability).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profileResponse_normalized_memLp`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profileResponse_normalized_memLp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real theta and every 3<=a<=b, the weighted response divided by sqrt(x) belongs to L2([a,b],dx). Rescaling to (0,1) shows measurability. Compact boundedness of the increments, 0<=rho<=1, and positivity of x^theta give a uniform bound by a constant times the L1 norm of g.

**Theorem 1.2 (Pointwise arithmetic error).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profile_weight_removal_pointwise`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profile_weight_removal_pointwise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<theta<1, assume the von Koch bound |E(x)|<=C*sqrt(x)*log(x)^2 eventually. The difference between weighted and unweighted responses is O(log(x)^2 times the integral of s*|g(s)| on (0,1)). The displacement bound 1-rho(x,u)<=4*u/x and the uniform von Koch bound for increments of length at most x^theta give this estimate for arbitrary integrable profiles.

**Theorem 1.3 (Negligible mean-square error from the variance band).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profile_weight_removal_l2`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profile_weight_removal_l2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a variance asymptotic uniform on the exponent band 0<alpha<theta<beta<1. The integral of the squared difference between weighted and unweighted responses against dx/x on [X,2X], divided by X^(1-theta)*log(X), tends to zero. No von Koch hypothesis is needed. The normalized error is bounded by 4/x times the integral of s*|g(s)|*|D(s*x^theta,x)|. Weighted Cauchy-Schwarz, Fubini, and the uniform moving-increment variance estimate bound its squared L2 norm by 16*C*norm(s*g,1)^2*X^(-2)*X*X^theta*log(X). The ratio to the mean-square scale is at most 16*C*norm(s*g,1)^2*X^(2*theta-2), which tends to zero.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profileResponse_normalized_memLp`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profile_weight_removal_l2`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profile_weight_removal_pointwise`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingIncrementVariance](MovingIncrementVariance.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity](MovingLengthRegularity.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/WeightControl](WeightControl.md)
