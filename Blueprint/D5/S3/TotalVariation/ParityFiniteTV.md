# Composition parity and biased Bernoulli parity

## Abstract

A uniform finite total-variation estimate for full parity vectors.

Let d and M be natural numbers with d>=2 and M>=3d. A full vector x is a function from Fin d to Bool, and h(x) is the number of its true coordinates. Put nu=M/(2M+d), eta=d/(2M+d), and pe=(1+(-1)^M eta^d)/2. The parity-conditioned Bernoulli mass is Q(x)=nu^h(x) (1-nu)^(d-h(x))/pe when h(x) mod 2=M mod 2, and zero otherwise. Independence belongs to the unconditioned product law; the conditioned coordinates are not asserted to be independent.

The composition parity mass R(x) is zero unless h(x)<=M and h(x) mod 2=M mod 2. On that support it equals choose((M-h(x))/2+d-1,d-1)/choose(M+d-1,d-1). These guarded natural-number binomial coefficients count the actual weak compositions with prescribed full parity vector. Both masses sum to one, and pe is positive.

**Theorem 1.1 (Uniform total-variation bound).**

Lean statement: `D5/S3/TotalVariation/ParityFiniteTV.parity_finite_tv`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityFiniteTV.parity_finite_tv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d>=2 and M>=3d, including both parities of M, one half of the sum over all full vectors x of |R(x)-Q(x)| is at most min(1,5(sqrt(d)/M+d(d-1)/M^2)). No normalization, moment, derivative, or total-variation estimate is required as an additional hypothesis.

Write tau=M/(M+d), m=d nu, and ell(z)=sum from j=1 to d-1 of log(M-z+2j)-z log(tau). The complete likelihood equals exp(ell(h)-ell(m)) divided by its Q-weighted finite mean. Integrating the decreasing reciprocal function at m cancels the Bernoulli bias and bounds the remaining discrete center slope by 1/(M-d). On the whole interval [0,d], the second derivative lies between -(d-1)/(M-d)^2 and zero. Convexity of the quadratic correction gives the two-sided remainder bound, including h<m and h=m, and the log-likelihood increment is uniformly at most one half.

The unconditioned product law has centered second moment d nu(1-nu). The center m is its mean, with no claim that m is the conditional mean. Since pe>=1/3, nonnegative parity truncation bounds the Q-centered second moment by 3d/4; finite Cauchy-Schwarz bounds the absolute centered first moment by sqrt(3d)/2. Consequently the Q-mean absolute log-likelihood increment is bounded by D=sqrt(3d)/(2(M-d))+3d(d-1)/(8(M-d)^2), which is less than one half.

Finite Jensen gives a likelihood normalizer at least exp(-D). The exponential mean-value estimate and the finite triangle inequality then bound total variation by exp(1)D. Comparing M-d with 2M/3 and using exp(1)<3 yields the coefficient 5. The additional bound by one follows from nonnegativity and the two exact mass sums.

## References

- Truth anchor: `D5/S3/TotalVariation/ParityFiniteTV.parity_finite_tv`
