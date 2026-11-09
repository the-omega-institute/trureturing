# Uniform common-band covariance

## Abstract

Uniform common-band covariance.

**Theorem 1.1 (Uniform common-band covariance).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandCovariance.common_band_covariance_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandCovariance.common_band_covariance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be locally bounded and measurable and satisfy the cumulative variance band asymptotic on 0<alpha<a<b<beta<1. One positive constant and one eventual threshold control every s,t in [0,1] and every interval [l,r] contained in [X,2X]: the absolute integral of D_(s*x^a)E(x)*D_(t*x^b)E(x) is at most C*X*X^a*log(X)*(1+(b-a)*log(X))^2. Write E as the residual at scale X^a, the terminal double average at a dyadic scale between X^b and 2X^b, and the intervening smoothing blocks. Bound the two residual pairings, the terminal term, and each block pair separately, then sum the quadratic number of pairs. All shifted function norms use containing intervals; the constants do not depend on the interval or profile parameters.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandCovariance.common_band_covariance_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs](DyadicCovariancePairs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/TranslationStripBounds](TranslationStripBounds.md)
