# Prime-Exponent Record Limit at One

## Abstract

For every fixed positive integer, strict prime-exponent record membership near one from the left is exactly membership in A029744 with the term three removed.

**Definition 1.1 (The prime-exponent score).**

$$\forall x \in \mathbb{R}, n \in \mathbb{N},\; f\left(x, n\right) = \sum_{p \in primeFactors\left(n\right)} real\left(factorization\left(n, p\right)\right)^{x}$$

*Formalization.* `D5/S3/Factorization/PrimeExponentRecordLimitOne.f` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real x and natural n, f(x,n) is the finite sum over the distinct prime divisors p of n of the real x-th power of the natural exponent of p in n. The displayed real coercion is part of the definition. OEIS A384669 (Switkay, 2025-06-06) supplies this score definition.

**Definition 1.2 (Strict record membership).**

$$\forall x \in \mathbb{R}, n \in \mathbb{N},\; (StrictRecord\left(x, n\right)) \Leftrightarrow ((1 \le n) \land (\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow ((m < n) \Rightarrow (f\left(x, m\right) < f\left(x, n\right)))))$$

*Formalization.* `D5/S3/Factorization/PrimeExponentRecordLimitOne.StrictRecord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

StrictRecord(x,n) requires n to be positive and f(x,n) to exceed f(x,m) for every positive natural m strictly below n. OEIS A384669 (Switkay, 2025-06-06) supplies this strict-record definition.

**Theorem 1.3 (The score at one).**

$$\forall n \in \mathbb{N},\; f\left(1, n\right) = real\left(cardFactors\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimeExponentRecordLimitOne.f_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At x=1 the score is Mathlib's cardFactors, the number of prime factors counted with multiplicity, by the factorization sum identity.

**Theorem 1.4 (The odd-part prime-product bound).**

$$\forall m \in \mathbb{N},\; ((m \ne 0) \land (Odd\left(m\right))) \Rightarrow (3^{length\left(primeFactorsList\left(m\right)\right)} \le m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimeExponentRecordLimitOne.odd_part_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero odd natural m, three raised to the length of its prime-factor list is at most m. Each listed prime is at least three, and the list product is m. Mathlib's cardFactors_apply identifies this length with the prime-factor count with multiplicity. The estimate supplies both the prime-product gap here and the odd-weight bound in JLTConjecture.

**Theorem 1.5 (The prime-product gap).**

$$\forall n \in \mathbb{N},\; ((n \ne 0) \land \left((\forall k \in \mathbb{N},\; n \ne 2^{k}) \land (\forall k \in \mathbb{N},\; n \ne 3 \cdot 2^{k})\right)) \Rightarrow (2^{cardFactors\left(n\right) + 1} < n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimeExponentRecordLimitOne.gap_lemma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If nonzero n is neither a power of two nor three times a power of two, then the power 2^(cardFactors(n)+1) is strictly smaller than n. Writing n as a power of two times an odd part, one odd prime at least five gives ratio at least 5/2, while at least two factors three give ratio at least 9/4. This gap lemma is repository-derived.

**Theorem 1.6 (Gap numbers are eventually excluded).**

$$\forall n \in \mathbb{N},\; ((n \ne 0) \land \left((\forall k \in \mathbb{N},\; n \ne 2^{k}) \land (\forall k \in \mathbb{N},\; n \ne 3 \cdot 2^{k})\right)) \Rightarrow (\exists delta \in \mathbb{R},\; (0 < delta) \land \left((delta < 1) \land (\forall x \in \mathbb{R},\; (1 - delta < x) \Rightarrow ((x < 1) \Rightarrow (\neg StrictRecord\left(x, n\right))))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimeExponentRecordLimitOne.eventually_not_record_of_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The smaller power of two supplied by the gap lemma has score cardFactors(n)+1 at x=1, strictly above the score of n. Continuity of the two finite score sums transports this defeat to a left neighborhood of one.

**Theorem 1.7 (Powers of two are eventual records).**

$$\forall k \in \mathbb{N},\; \exists delta \in \mathbb{R},\; (0 < delta) \land \left((delta < 1) \land (\forall x \in \mathbb{R},\; (1 - delta < x) \Rightarrow ((x < 1) \Rightarrow (StrictRecord\left(x, 2^{k}\right))))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimeExponentRecordLimitOne.eventually_two_pow_record` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive predecessor of 2^k has fewer than k prime factors counted with multiplicity. The finitely many strict inequalities at x=1 therefore persist simultaneously on a left neighborhood of one; k=0 is vacuous.

**Theorem 1.8 (Strict subadditivity below one).**

$$\forall k \in \mathbb{N}, x \in \mathbb{R},\; ((0 < k) \land \left((0 < x) \land (x < 1)\right)) \Rightarrow (real\left(k + 1\right)^{x} < real\left(k\right)^{x} + 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimeExponentRecordLimitOne.strict_subadditive_rpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive natural k and real 0<x<1, strict concavity gives (k+1)^x < k^x+1. The proof obtains the strict inequality via Mathlib's Real.strictConcaveOn_rpow; this supporting bridge is repository-derived, not a newly asserted classical result.

**Theorem 1.9 (Three is never a positive-exponent record).**

$$\forall x \in \mathbb{R},\; (0 < x) \Rightarrow (\neg StrictRecord\left(x, 3\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimeExponentRecordLimitOne.not_record_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real exponent, two and three both have score one. Since two is a smaller positive integer, three cannot be a strict record.

**Theorem 1.10 (Three times a positive power of two is an eventual record).**

$$\forall k \in \mathbb{N},\; (0 < k) \Rightarrow (\exists delta \in \mathbb{R},\; (0 < delta) \land \left((delta < 1) \land (\forall x \in \mathbb{R},\; (1 - delta < x) \Rightarrow ((x < 1) \Rightarrow (StrictRecord\left(x, 3 \cdot 2^{k}\right))))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimeExponentRecordLimitOne.eventually_three_two_record` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Below 3*2^k, any number with fewer than k+1 prime factors loses already at one. The only smaller number with exactly k+1 factors is 2^(k+1), and strict subadditivity breaks that tie in favor of 3*2^k for 0<x<1.

**Definition 1.11 (The endpoint candidate family).**

$$\forall n \in \mathbb{N},\; (Candidate\left(n\right)) \Leftrightarrow (((\exists k \in \mathbb{N},\; n = 2^{k}) \lor (\exists k \in \mathbb{N},\; (1 \le k) \land (n = 3 \cdot 2^{k}))))$$

*Formalization.* `D5/S3/Factorization/PrimeExponentRecordLimitOne.Candidate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Candidate(n) means that n is a power of two, or is three times 2^k for a positive natural k. Thus the definition is exactly A029744 with its term three omitted. OEIS A029744 supplies the powers-of-two and three-times-powers-of-two family.

**Theorem 1.12 (The A384669 endpoint at one).**

$$\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\exists delta \in \mathbb{R},\; (0 < delta) \land \left((delta < 1) \land (\forall x \in \mathbb{R},\; (1 - delta < x) \Rightarrow ((x < 1) \Rightarrow ((StrictRecord\left(x, n\right)) \Leftrightarrow (((\exists k \in \mathbb{N},\; n = 2^{k}) \lor (\exists k \in \mathbb{N},\; (1 \le k) \land (n = 3 \cdot 2^{k})))))))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimeExponentRecordLimitOne.a384669_endpoint_limit_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed positive n there is a real 0<delta<1 such that, whenever 1-delta<x<1, n is a strict record exactly when it is a power of two or three times a positive power of two. The power-of-two, three-times-power, three, and gap cases exhaust the positive naturals. This is limited to the per-n eventual formulation: no uniform delta and no sequence-level limit are claimed. OEIS A384669 supplies the sequence-level conjectural target; the per-n quantifiers proved here are repository-derived.

## References

- Truth anchor: `D5/S3/Factorization/PrimeExponentRecordLimitOne.Candidate`
- Truth anchor: `D5/S3/Factorization/PrimeExponentRecordLimitOne.StrictRecord`
- Truth anchor: `D5/S3/Factorization/PrimeExponentRecordLimitOne.a384669_endpoint_limit_one`
- Truth anchor: `D5/S3/Factorization/PrimeExponentRecordLimitOne.eventually_not_record_of_gap`
- Truth anchor: `D5/S3/Factorization/PrimeExponentRecordLimitOne.eventually_three_two_record`
- Truth anchor: `D5/S3/Factorization/PrimeExponentRecordLimitOne.eventually_two_pow_record`
- Truth anchor: `D5/S3/Factorization/PrimeExponentRecordLimitOne.f`
- Truth anchor: `D5/S3/Factorization/PrimeExponentRecordLimitOne.f_one`
- Truth anchor: `D5/S3/Factorization/PrimeExponentRecordLimitOne.gap_lemma`
- Truth anchor: `D5/S3/Factorization/PrimeExponentRecordLimitOne.not_record_three`
- Truth anchor: `D5/S3/Factorization/PrimeExponentRecordLimitOne.odd_part_lower`
- Truth anchor: `D5/S3/Factorization/PrimeExponentRecordLimitOne.strict_subadditive_rpow`
