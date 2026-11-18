# Sharp upper counts for Robin exceptions

## Abstract

The ordinary Robin exceptions and the real-power Robin exceptions uniformly above a fixed positive parameter gap have upper count exp((C0+epsilon)*log(x)/log(log(x))).

**Definition 1.1 (The real-power divisor transform).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.sigmaKappa`

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.sigmaKappa` (`✓ std3`).

*Citation.* Steve Fan, Mits Kobayashi, Grant Molnar (2025). *A family of analogues to the Robin criterion*. DOI: [10.1007/s11139-026-01408-3](https://doi.org/10.1007/s11139-026-01408-3). URL: <https://arxiv.org/abs/2511.02106v1>.

*Commentary.*

The transform sigmaKappa(kappa,n) is the divisor sum of mu(n/d)*sigma(d)^kappa. The real-power Robin inequality uses the real part of zeta(kappa) times this transform and compares it with (exp(gamma)*n*log(log(n)))^kappa. Fan, Kobayashi and Molnar suggest considering real-power analogues of the Robin exception-count results in Section 8.

**Definition 1.2 (The large distinct-prime tail).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.tailCount`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.tailCount` (`✓ std3`).

*Citation.* Florian Luca, Carl Pomerance, Patrick Solé (2025). *Correction to: On Robin's inequality*. URL: <https://math.dartmouth.edu/~carlp/robin4.pdf>.

*Commentary.*

The function tailCount(lambda,x) counts positive integers up to x whose number of distinct prime factors exceeds log(x)/log(log(x))+lambda*log(x)/(log(log(x)))^2. The cited correction connects Robin exceptions with the distinct-prime tail at lambda=0 and supplies the necessary-condition motivation for this statistic. The second-order threshold, optimized constant C0 and sharp tail rate are repository-derived results, reused in the two conclusions below.

**Theorem 1.3 (Uniform real-power Robin exception bound).**

Lean statement: `D5/S3/Arith/Robin/Analytic/RobinExceptionCount.kappa_exception_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/RobinExceptionCount.kappa_exception_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every delta>0 and epsilon>0, the number of natural n with 2162160<n<=x for which some real kappa>=1+delta satisfies zeta(kappa)*sigmaKappa(kappa,n)>=(exp(gamma)*n*log(log(n)))^kappa is eventually at most exp((C0+epsilon)*log(x)/log(log(x))). The quantifier over kappa is inside the exceptional predicate, so one common eventual bound covers the entire unbounded parameter range. Prime-power factor bounds and ordered prime-factor replacement compare the normalized transform with the initial prime product and a uniformly controlled convergent Euler tail. A quantitative Mertens remainder and a second-order prime-counting estimate leave a strict inverse-logarithmic gap below the Robin threshold. The resulting local distinct-prime exclusion transfers to the global count through a finite initial segment and dyadic intervals. This is an unconditional upper bound; it asserts neither existence nor an asymptotic lower count of exceptions.

**Theorem 1.4 (Ordinary Robin exception bound).**

Lean statement: `D5/S3/Arith/Robin/Analytic/RobinExceptionCount.robin_exception_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/RobinExceptionCount.robin_exception_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every epsilon>0, the number of natural n with 5040<n<=x and sigma(n)>=exp(gamma)*n*log(log(n)) is eventually at most exp((C0+epsilon)*log(x)/log(log(x))). The ordinary divisor ratio is bounded by the inverse Euler product over its distinct prime factors, and replacing those primes by the first primes gives the same strict Mertens gap used in the real-power argument. The proved local exclusion and the existing sharp distinct-prime tail upper bound supply the global count. Equality belongs to the exceptional set. The theorem does not assert the Robin inequality for every n>5040.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.sigmaKappa`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTailUpper.tailCount`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/RobinExceptionCount.kappa_exception_count`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/RobinExceptionCount.robin_exception_count`
- Dependency: [D5/S3/Arith/Robin/Analytic/ExceptionCount/CountingTransfer](ExceptionCount/CountingTransfer.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/ExceptionCount/MertensGap](ExceptionCount/MertensGap.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionArithmetic](ExceptionCount/ReductionArithmetic.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/ExceptionCount/ZetaTail](ExceptionCount/ZetaTail.md)
