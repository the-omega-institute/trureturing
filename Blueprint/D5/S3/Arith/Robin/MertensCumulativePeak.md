# A cumulative Mertens peak and a Robin witness

## Abstract

A cumulative second-Mertens peak produces a bounded strict Robin witness at an actual prefix lcm.

**Theorem 1.1 (A finite bound for an actual integer witness).**

Lean statement: `D5/S3/Arith/Robin/MertensCumulativePeak.mertens_cumulative_peak_robin_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/MertensCumulativePeak.mertens_cumulative_peak_robin_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x at least 10000 squared, if the integral of Mertens.E₂p from 2 to x exceeds 12*sqrt(x)*log(x), there is a real t in [10000,x] such that N=lcm(1,...,floor(t)) satisfies 5040<N<=exp(x*log(x)) and sigma(N)/N>exp(gamma)*log(log(N)). The only premises are the lower bound on x and the strict cumulative-peak inequality; gamma is the real Euler constant.

The reference input is the cumulative-peak proposition in section 477 of FIBONACCI_ANALYTIC_FRONTIER_INTERFACES. Its constant c₂=gamma−sum_p sum_(k>=2) 1/(k*p^k) is Mertens.M: Mertens.M.eq gives M=gamma+sum_p(log(1−1/p)+1/p), with the prime-power expansion identified by tsum_M_eq_f_eq_tsum. Thus the reference's E₂ is exactly Mertens.E₂p, and its Delta₁(x) is the interval integral used in the theorem.

Put a=10000. Write I(u)=(theta(u)−u)/(u*log(u))−E₂p(u), q(u)=u*log(u)/(1+log(u)), and h(u)=log(u)/(1+log(u))². Finite Abel summation and integration by parts for an absolutely continuous primitive give Delta₁(x)=Delta₁(a)+q(a)*I(a)−q(x)*I(x)−integral_a^x h(u)*I(u) du. This uses no pointwise derivative at a prime.

For u>=2, the correction E₃(u)+E₂p(u) has absolute value at most 4/u. If the strict Mertens response fails throughout [a,x], the common lcm response and the Chebyshev psi-minus-theta bound give I(u)>=−10/sqrt(u)>=−6*log(u)/sqrt(u). The general Mertens estimates give |E₂p(u)|<=20 for u>=2, hence Delta₁(a)+q(a)*I(a)<=41*a at a=10000. The endpoint and integral terms are bounded by 6*sqrt(x)*log(x) and 12*sqrt(x). Since sqrt(x)>=10000 and log(x)>10, their total is strictly below the assumed peak. The resulting strict response supplies the lcm witness, and t*log(t)<=x*log(x) gives its size bound.

## References

- Truth anchor: `D5/S3/Arith/Robin/MertensCumulativePeak.mertens_cumulative_peak_robin_witness`
- Dependency: [D5/S3/Arith/Robin/ActualRobinClockCovariance](ActualRobinClockCovariance.md)
- Dependency: [D5/S3/Arith/Robin/LcmRobinResponse](LcmRobinResponse.md)
