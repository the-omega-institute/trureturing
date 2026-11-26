# A classical Chebyshev lower bound in one residue class

## Abstract

Primes congruent to one modulo four supply the Euler-form denominator.

**Definition 1.1 (Counting primes in the residue class).**

Lean statement: `D5/S3/PrimeGaps/ModFourChebyshev.primeCount`

*Formalization.* `D5/S3/PrimeGaps/ModFourChebyshev.primeCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count includes the primes p with 1 <= p <= floor(x) and p congruent to one modulo four.

**Remark 1.2 (The classical weighted Mertens estimate).**

Lean statement: `D5/S3/PrimeGaps/ModFourChebyshev.prime_count_lower`

*Formalization.* `D5/S3/PrimeGaps/ModFourChebyshev.prime_count_lower` (`✓ std3`).

*Citation.* Tom M. Apostol (1976). *Introduction to Analytic Number Theory*. DOI: [10.1007/978-1-4757-5579-4](https://doi.org/10.1007/978-1-4757-5579-4).

*Commentary.*

Apostol, Introduction to Analytic Number Theory, Chapter 7, Theorem 7.3 (p. 148), states that for k > 0 and gcd(h,k) = 1, the sum of log(p)/p over primes p <= x with p congruent to h modulo k is log(x)/phi(k) + O(1). The case k = 4, h = 1 gives half log(x) + O(1). This attribution concerns the classical statement; the constant twelve and the prime-count lower bound below are repo-derived.

**Theorem 1.3 (A lower bound for every sufficiently large threshold).**

Lean statement: `D5/S3/PrimeGaps/ModFourChebyshev.prime_count_lower`

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/ModFourChebyshev.prime_count_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tom M. Apostol (1976). *Introduction to Analytic Number Theory*. DOI: [10.1007/978-1-4757-5579-4](https://doi.org/10.1007/978-1-4757-5579-4).

*Commentary.*

The ordinary weighted Mertens estimate and the bounded character-weighted Mangoldt sum give a modulus-four weighted prime sum within twelve of half log(x). The prime-power correction is bounded by the existing convergent correction series. The explicit error constant twelve is a repo-derived quantitative form of the classical estimate.

Apply the weighted estimate at x and at x/exp(50). For x at least exp(50), their difference is at least one. Every prime in the resulting fixed-ratio window is greater than x/exp(50), and log(p) is at most log(x). Hence the count is at least exp(-50)*x/log(x) for every such x. The threshold exp(50) and this fixed-ratio window deduction are repo-derived explicit quantitative choices.

## References

- Truth anchor: `D5/S3/PrimeGaps/ModFourChebyshev.primeCount`
- Truth anchor: `D5/S3/PrimeGaps/ModFourChebyshev.prime_count_lower`
- Truth anchor: `D5/S3/PrimeGaps/ModFourChebyshev.prime_count_lower`
- Dependency: [D5/S3/PrimeGaps/ChiFourWeightedMangoldt](ChiFourWeightedMangoldt.md)
- Dependency: [D5/S3/Weil/Mertens/Estimates](../Weil/Mertens/Estimates.md)
