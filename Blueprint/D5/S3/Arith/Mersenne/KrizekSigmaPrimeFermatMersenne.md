# Krizek's A249759 Fermat-Mersenne Classification

## Abstract

Prime divisor sums force a prime-power input and the Fermat-Mersenne forms conjectured for OEIS A249759.

**Theorem 1.1 (A prime divisor sum has prime-power input).**

$$\forall m \in \mathbb{N},\; (\operatorname{Prime}\left(\operatorname{sigma}_1(m)\right)) \Rightarrow (\exists q \in \mathbb{N}, k \in \mathbb{N},\; (\operatorname{Prime}\left(q\right)) \land \left((1 \le k) \land (m = q^{k})\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Mersenne/KrizekSigmaPrimeFermatMersenne.sigma_one_prime_imp_prime_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jaroslav Krizek (2014). *OEIS A249759, primes p for which sigma(p-1) is prime*. URL: <https://oeis.org/A249759>.

*Commentary.*

All variables are natural numbers. The named operator sigma with subscript one is the sum-of-divisors function, so sigma sub one of m sums the first powers of all positive divisors of m. If this value is prime, the multiplicative factorization over all prime divisors of m forces that set to have one member. Thus m is a positive power of a prime.

**Theorem 1.2 (A249759 primes have Fermat and Mersenne form).**

$$\forall p \in \mathbb{N},\; ((\operatorname{Prime}\left(p\right)) \land (\operatorname{Prime}\left(\operatorname{sigma}_1(p - 1)\right))) \Rightarrow ((\exists m \in \mathbb{N},\; p = 2^{2^{m}} + 1) \land (\exists r \in \mathbb{N},\; (\operatorname{Prime}\left(r\right)) \land (\operatorname{sigma}_1(p - 1) = 2^{r} - 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Mersenne/KrizekSigmaPrimeFermatMersenne.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a249759-krizek-sigma-prime-fermat-mersenne` (proved) by `D5/S3/Arith/Mersenne/KrizekSigmaPrimeFermatMersenne.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a249759-krizek-sigma-prime-fermat-mersenne","declaration_gid":"D5/S3/Arith/Mersenne/KrizekSigmaPrimeFermatMersenne.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jaroslav Krizek (2014). *OEIS A249759, primes p for which sigma(p-1) is prime*. URL: <https://oeis.org/A249759>.

*Commentary.*

Here sigma sub one has the same divisor-sum convention. The hypotheses exclude p equal to two because sigma sub one of one is one; hence natural subtraction in p minus one is not truncated. The preceding prime-power theorem makes p minus one a power of two. Primality of p makes its exponent a power of two, while primality of the geometric divisor sum makes the Mersenne exponent prime. This proves items 2 and 3 of the cited conjecture only.

## References

- Truth anchor: `D5/S3/Arith/Mersenne/KrizekSigmaPrimeFermatMersenne.result`
- Truth anchor: `D5/S3/Arith/Mersenne/KrizekSigmaPrimeFermatMersenne.sigma_one_prime_imp_prime_pow`
