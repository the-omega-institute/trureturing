# Removing the price weight from profiles

## Abstract

Price removal for integrable moving profiles has a negligible mean-square error.

**Theorem 1.1 (Uniform bound for the price-weighted profile integral).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.weighted_profile_integral_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.weighted_profile_integral_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an integrable profile g, x>=3, and a nonnegative uniform bound M for abs(E(x+s*x^theta)-E(x)) on 0<=s<=1, the absolute unit integral of g(s) times this increment times priceRatio(x,s*x^theta) is at most profileL1(g)*M. The price ratio lies between zero and one.

Let E be locally bounded and Borel measurable, let g be an integrable Borel profile on (0,1), and put H(x)=x^theta. The unweighted response is sqrt(x)*P(H(x),g,x), where P is the profile average. The weighted response inserts rho(x,u)=w(x+u)/w(x) into the defining integral.

**Theorem 1.2 (Joint measurability of the price ratio).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.price_measurable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.price_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map (x,u) to w(x+u)/w(x) is Borel measurable, using the explicit logarithmic formula for w.

**Theorem 1.3 (Exact unit-profile representation).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.normalized_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.normalized_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x>0 and any real exponent theta, the weighted profile response divided by sqrt(x) equals x^(-theta) times the integral over s in (0,1) of g(s), the increment E(x+s*x^theta)-E(x), and the price ratio at that displacement. This is the change of variables u=s*x^theta in the defining profile integral.

**Theorem 1.4 (Uniform compact bound for moving increments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.local_increment_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.local_increment_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For locally bounded measurable E, any real theta and 0<a<=b, there is M>=0 bounding the absolute value of E(x+s*x^theta)-E(x) simultaneously for a<=x<=b and 0<=s<=1. Continuity bounds x^theta on the compact spatial interval, and local boundedness controls both endpoints.

**Theorem 1.5 (Joint measurability of moving increments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.increment_measurable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.increment_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For locally bounded Borel measurable E and every real theta, the map (x,s) to E(x+s*x^theta)-E(x) is Borel measurable. This follows by composing E with the measurable endpoint maps and subtracting.

**Theorem 1.6 (Local square integrability).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profileResponse_normalized_memLp`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profileResponse_normalized_memLp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real theta and every 3<=a<=b, the weighted response divided by sqrt(x) belongs to L2([a,b],dx). Rescaling to (0,1) shows measurability. Compact boundedness of the increments, 0<=rho<=1, and positivity of x^theta give a uniform bound by a constant times the L1 norm of g.

**Theorem 1.7 (Measurability of the weighted response).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profileResponse_aestronglyMeasurable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profileResponse_aestronglyMeasurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For locally bounded Borel measurable E, an integrable Borel profile g, any real theta and 3<=a<=b, the weighted profile response is almost everywhere strongly measurable on (a,b] with respect to Lebesgue measure. Multiply the already square-integrable response divided by sqrt(x) by the continuous function sqrt(x).

**Theorem 1.8 (Pointwise arithmetic error).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profile_weight_removal_pointwise`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profile_weight_removal_pointwise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<theta<1, assume the von Koch bound |E(x)|<=C*sqrt(x)*log(x)^2 eventually. The difference between weighted and unweighted responses is O(log(x)^2 times the integral of s*|g(s)| on (0,1)). The displacement bound 1-rho(x,u)<=4*u/x and the uniform von Koch bound for increments of length at most x^theta give this estimate for arbitrary integrable profiles.

**Theorem 1.9 (Negligible mean-square error from the variance band).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profile_weight_removal_l2`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profile_weight_removal_l2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a variance asymptotic uniform on the exponent band 0<alpha<theta<beta<1. The integral of the squared difference between weighted and unweighted responses against dx/x on [X,2X], divided by X^(1-theta)*log(X), tends to zero. No von Koch hypothesis is needed. The normalized error is bounded by 4/x times the integral of s*|g(s)|*|D(s*x^theta,x)|. Weighted Cauchy-Schwarz, Fubini, and the uniform moving-increment variance estimate bound its squared L2 norm by 16*C*norm(s*g,1)^2*X^(-2)*X*X^theta*log(X). The ratio to the mean-square scale is at most 16*C*norm(s*g,1)^2*X^(2*theta-2), which tends to zero.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.increment_measurable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.local_increment_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.normalized_eq`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.price_measurable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profileResponse_aestronglyMeasurable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profileResponse_normalized_memLp`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profile_weight_removal_l2`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.profile_weight_removal_pointwise`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.weighted_profile_integral_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingIncrementVariance](MovingIncrementVariance.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity](MovingLengthRegularity.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/WeightControl](WeightControl.md)
