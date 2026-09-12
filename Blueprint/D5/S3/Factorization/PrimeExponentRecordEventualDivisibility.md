# Eventual Divisibility of Prime-Exponent Records

## Abstract

Every positive integer divides every sufficiently large strict record of the prime-exponent score when the real exponent lies strictly between zero and one.

**Theorem 1.1 (Prime exponents decrease along the ordered primes).**

$$\forall x \in \mathbb{R}, n \in \mathbb{N}, p \in \mathbb{N}, q \in \mathbb{N},\; ((0 < x) \land \left((StrictRecord\left(x, n\right)) \land \left((Prime\left(p\right)) \land \left((Prime\left(q\right)) \land (p < q)\right)\right)\right)) \Rightarrow (factorization\left(n, q\right) \le factorization\left(n, p\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimeExponentRecordEventualDivisibility.strictRecord_factorization_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a strict record, the exponent at a larger prime is at most the exponent at a smaller prime. Otherwise transferring the exponent difference from the larger prime to the smaller one produces a smaller positive integer with the same score. The prime-power theorem uses this order to obtain a uniform exponent bound.

**Theorem 1.2 (Every fixed prime power eventually divides the records).**

$$\forall x \in \mathbb{R},\; (0 < x) \Rightarrow ((x < 1) \Rightarrow (\forall p \in \mathbb{N}, a \in \mathbb{N},\; (Prime\left(p\right)) \Rightarrow (\exists N \in \mathbb{N},\; \forall n \in \mathbb{N},\; (N \le n) \Rightarrow ((StrictRecord\left(x, n\right)) \Rightarrow (p^{a} \mid n)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimeExponentRecordEventualDivisibility.eventually_prime_power_dvd_records` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real 0<x<1 and a fixed prime power p^a, all sufficiently large strict records are divisible by p^a. If the p-exponent is below a, a transfer at each smaller prime combines a positive one-step gain with the fixed-step loss E^x-(E-c)^x, which tends to zero. The exponent order then bounds every prime exponent by a common B. A further bound C excludes prime factors above 2^C, leaving only finitely many records.

**Theorem 1.3 (Every positive integer eventually divides the records).**

$$\forall x \in \mathbb{R},\; (0 < x) \Rightarrow ((x < 1) \Rightarrow (\forall d \in \mathbb{N},\; (1 \le d) \Rightarrow (\exists N \in \mathbb{N},\; \forall n \in \mathbb{N},\; (N \le n) \Rightarrow ((StrictRecord\left(x, n\right)) \Rightarrow (d \mid n)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimeExponentRecordEventualDivisibility.prime_exponent_record_eventual_divisibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real 0<x<1 and every natural d>=1, there is a natural threshold N such that d divides every strict prime-exponent record n>=N. The proof takes the maximum of the prime-power thresholds for the finitely many prime factors of d. The chosen N is a sufficient threshold depending on x and d. This implementation obtains intermediate bounds B and C with Classical.choose; the document does not extract an executable procedure for computing N or address the least threshold.

OEIS A384669 revision #6, submitted by Hal M. Switkay on 2025-06-08, states this conjecture. The proofs in this document are repository-derived. No claim of a first proof or of an unresolved present status is made; subsequent literature was not systematically searched.

## References

- Truth anchor: `D5/S3/Factorization/PrimeExponentRecordEventualDivisibility.eventually_prime_power_dvd_records`
- Truth anchor: `D5/S3/Factorization/PrimeExponentRecordEventualDivisibility.prime_exponent_record_eventual_divisibility`
- Truth anchor: `D5/S3/Factorization/PrimeExponentRecordEventualDivisibility.strictRecord_factorization_antitone`
- Dependency: [D5/S3/Factorization/PrimeExponentRecordLimitOne](PrimeExponentRecordLimitOne.md)
