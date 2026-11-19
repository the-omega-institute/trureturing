# Distinct-prime tail upper bounds

## Abstract

The upper tail of the number of distinct prime factors has an optimized Rankin exponent and a vanishing exponent at its second-order endpoint.

**Definition 1.1 (Logarithmic scale).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.scale`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.scale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scale y(x) is log(x)/log(log(x)). It is positive and tends to infinity for sufficiently large positive x.

**Definition 1.2 (Second-order threshold).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.threshold`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.threshold` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The threshold T(lambda,x) equals y(x)+lambda*y(x)/log(log(x)). The parameter lambda is fixed before x tends to infinity.

**Definition 1.3 (Counting distinct-prime tails).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.tailCount`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.tailCount` (`✓ std3`).

*Citation.* Florian Luca, Carl Pomerance, Patrick Solé (2025). *Correction to: On Robin's inequality*. URL: <https://math.dartmouth.edu/~carlp/robin4.pdf>.

*Commentary.*

The finite count includes exactly the positive natural numbers n not exceeding the real cutoff x whose number of distinct prime divisors exceeds T(lambda,x). The statistic is cardDistinctFactors, rather than the number of prime factors with multiplicity. The cited correction uses the distinct-prime tail at lambda=0 as a necessary condition on Robin exceptions. The second-order threshold and estimates here are repository-derived; the source is not claimed to prove them.

**Definition 1.4 (Optimizing root).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.a`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For s>1, a(s)=s*sin(pi/s)/pi is positive. The optimizing Rankin parameter is c=a(s)^s.

**Definition 1.5 (Optimized rate).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.rate`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.rate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rate F(lambda,s) is s*(1-lambda-log(a(s))). It arises from I(s,c)-log(c)-s*lambda, where I(s,c)=pi*c^(1/s)/sin(pi/s), upon setting c=a(s)^s.

**Theorem 1.6 (Positive scale).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.scale_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.scale_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If x>exp(1), then scale(x)>0. This positivity is used to transfer normalized inequalities back to counting and logarithmic product costs.

**Theorem 1.7 (Growing scale).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.scale_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.scale_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithmic counting scale tends to positive infinity as x tends to positive infinity. It is reused for exact bin cardinalities and entropy asymptotics.

**Theorem 1.8 (Positive optimizing root).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.a_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.a_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every s>1, a(s)>0. The density normalization and the minimum-rate argument use this same optimizing root.

**Theorem 1.9 (Power kernel integral).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.power_kernel_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.power_kernel_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For s>1 and c>0, the function s*c/(u^s+c) is integrable on u>0 and its integral is pi*c^(1/s)/sin(pi/s). This evaluates the mass of the lower-bound density.

**Definition 1.10 (Logarithmic weight).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.logWeight`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.logWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The logarithmic weight at s,z,t is log(1+z/t^s).

**Definition 1.11 (Abel kernel).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.abelKernel`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.abelKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Abel kernel at s,z,t is s*z/(t*(t^s+z)).

**Theorem 1.12 (Logarithmic weight derivative).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.logWeight_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.logWeight_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For z>0 and t>0, the logarithmic weight has derivative minus the Abel kernel. The entropy integral uses this derivative with its endpoint limits.

**Theorem 1.13 (Finite Rankin exponential bound).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.rankin_exponential_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.rankin_exponential_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For s>1, z>=1 and x>0, count the integers n from 1 through floor(x) whose distinct-prime count is strictly greater than the real threshold T.

This count is bounded by exp((s*log(x) - T*log(z)) + log(1 + the p-series of exponent s) + the sum of log(1+z*p^(-s)) over primes at most x). The estimate applies even at a zero count.

**Theorem 1.14 (Rankin upper bound).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed real lambda<=1, s>1 and epsilon>0, eventually N(lambda,x)<=exp((F(lambda,s)+epsilon)*y(x)). No parameter s depending on x is used.

The finite-support Euler expansion bounds the weighted integer sum by a product over primes at most x. The inverse unweighted factors are bounded by a convergent positive Dirichlet series. At z=c*log(x)^s, the logarithmic prefactor divided by y(x) tends to -log(c)-s*lambda.

For each fixed alpha in (0,1), primes up to log(x)^alpha contribute o(y(x)). Above that cutoff, the prime number theorem gives a uniform linear bound for prime counting. Abel summation compares the remaining weighted sum with the positive integral of s*c/(u^s+c). A power substitution and the existing Beta normalizer evaluate that integral exactly. Choosing alpha sufficiently close to one preserves the stated coefficient.

**Theorem 1.15 (Vanishing exponent at the endpoint).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At lambda=1, log(1+N(1,x))/y(x) tends to zero. The quotient is eventually nonnegative. For fixed s at least pi, the cubic sine bound and an elementary logarithm inequality give 0<=F(1,s)<=pi^2/(3*s). First apply the upper bound with this fixed s, then choose s sufficiently large. The additive log(2)/y(x) tends to zero. This is an unconditional counting statement and does not decide any pointwise Robin inequality. The matching lower bound at lambda=0 is proved separately in OmegaTail.Asymptotic.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.a`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.a_pos`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.abelKernel`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.logWeight`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.logWeight_deriv`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.power_kernel_integral`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.rankin_exponential_bound`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.rate`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.result`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.scale`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.scale_pos`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.scale_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.tailCount`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.threshold`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.upper_bound`
- Dependency: [D5/S3/Arith/Robin/EulerLayerRootCorrection](../EulerLayerRootCorrection.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/PrimeBoundarySecondOrder](../PriceRecord/PrimeBoundarySecondOrder.md)
- Dependency: [D5/S3/Quantum/Divergence/EntropyDefectInverseSqrtStability](../../../Quantum/Divergence/EntropyDefectInverseSqrtStability.md)
