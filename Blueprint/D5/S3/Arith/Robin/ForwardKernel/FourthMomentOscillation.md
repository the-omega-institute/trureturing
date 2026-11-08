# Two-sided profile oscillation

## Abstract

Variance asymptotics and a fourth moment bound give positive proportions of both signs on each sufficiently large dyadic interval.

**Theorem 1.1 (Positive proportions for both strict tails).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentOscillation.profile_response_two_sided_positive_proportion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthMomentOscillation.profile_response_two_sided_positive_proportion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be locally bounded and measurable, let 0<alpha<theta<beta<1, and assume the cumulative variance asymptotic and the fourth moment band bound for E on this exponent band. For every real integrable profile g on (0,1) that is not almost everywhere zero, there is B>0 depending only on alpha, theta, and beta. Put K=B*C4*profileL1(g)^4>0 and v=(2^(1-theta)-1)*Q(g)/2, K1=8*(K+v^2/4), Lambda=(v/2)^(3/2)/sqrt(K1), c=Lambda/8, and delta=Lambda^2/(16*sqrt(K1)). For every sufficiently large X, each of the sets where the profile response exceeds c*sqrt(S_X) or is below -c*sqrt(S_X) has logarithmic probability at least delta, where S_X=X^(1-theta)*log(X) and the probability density on (X,2X] is 1/(x*log(2)). Both c and delta are strictly positive.

Normalize the response by sqrt(S_X). The dyadic mean-square asymptotic gives a second moment tending to Q(g)*(2^(1-theta)-1)/log(2)>v. The profile fourth moment bound eventually bounds the fourth moment of the normalized response by K=B*C4*profileL1(g)^4. The positive second-moment lower bound and Cauchy-Schwarz force K>=v^2>0. The normalized first moment tends to zero by choosing the intermediate exponent (theta+beta)/2. Local boundedness of E ensures all required moments are integrable. Applying the general two-sided moment inequality and multiplying the strict thresholds by sqrt(S_X)>0 gives the two asserted proportions.

This result assumes the abstract variance and fourth-moment hypotheses; the conditional arithmetic Corollaries 493.4–493.5 are outside its scope.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentOscillation.profile_response_two_sided_positive_proportion`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareAsymptotic](DyadicMeanSquareAsymptotic.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/DyadicProbability](DyadicProbability.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthMomentMean](FourthMomentMean.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthMomentMovingBounds](FourthMomentMovingBounds.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthMomentProbability](FourthMomentProbability.md)
