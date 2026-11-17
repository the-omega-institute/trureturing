# Kline's Factorial and Prefix Lcm Totient Quotient

## Abstract

Kline's A025527 quotient equals the totient quotient at every positive integer prime index.

**Definition 1.1 (The independent factorial quotient).**

$$\forall m \in \mathrm{Nat},\; a\left(m\right) = \frac{(m)!}{L\left(m\right)}$$

*Formalization.* `D5/S3/Factorization/KlineFactorialLcmTotient.a` (`✓ std3`).

*Citation.* Fred Daniel Kline (2017). *OEIS A025527: n!/lcm(1,2,...,n), prime-minus-one totient quotient conjecture*. URL: <https://oeis.org/A025527/internal>.

*Commentary.*

For each natural m, a(m) is m! divided by the least common multiple L(m) of the integers 1 through m. The quotient is taken in the rationals, and is defined independently of Euler's totient.

**Theorem 1.2 (The totient quotient at every prime minus one).**

$$\forall j \in \mathrm{Int},\; 1 \le j \Rightarrow a\left(nth\left(Prime, toNat\left(j\right)-1\right)-1\right) = \frac{phi\left((nth\left(Prime, toNat\left(j\right)-1\right)-1)!\right)}{phi\left(L\left(nth\left(Prime, toNat\left(j\right)-1\right)-1\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/KlineFactorialLcmTotient.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a025527-kline-prime-minus-one-totient-quotient` (proved) by `D5/S3/Factorization/KlineFactorialLcmTotient.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a025527-kline-prime-minus-one-totient-quotient","declaration_gid":"D5/S3/Factorization/KlineFactorialLcmTotient.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Fred Daniel Kline (2017). *OEIS A025527: n!/lcm(1,2,...,n), prime-minus-one totient quotient conjecture*. URL: <https://oeis.org/A025527/internal>.

*Commentary.*

For every integer j at least one, p is the j-th prime and m=p-1. Here p is Nat.nth Nat.Prime (j.toNat-1), translating the one-based integer index to the zero-based enumeration of all primes. Then a(m)=phi(m!)/phi(L(m)), with both ratios in the rationals. The case j=1 gives p=2 and m=1, with phi(1)=1. The factorial and prefix lcm have exactly the same prime divisors. Euler's prime-factor product for the totient therefore supplies a common multiplicative factor; the positive denominators permit cancellation. This mechanism does not use primality of p, although the stated domain is precisely Kline's prime-minus-one sequence.

## References

- Truth anchor: `D5/S3/Factorization/KlineFactorialLcmTotient.a`
- Truth anchor: `D5/S3/Factorization/KlineFactorialLcmTotient.result`
