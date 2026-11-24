# Ordered prime supports for the character sieve

## Abstract

Ordered prime supports for the character sieve

**Theorem 1.1 (Successor ranks below a prime).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_succ_le_of_prime`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_succ_le_of_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the k-th prime is less than a prime p, the next prime is at most p. This successor step supports the lower bound for sorted prime lists.

**Theorem 1.2 (Prime ranks in a sorted list).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_le_get`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_le_get` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any strictly increasing list of primes, its entry at index i is at least the i-th prime. The statement covers every index below the list length.

**Theorem 1.3 (The prime at index five).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_five`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With zero-based indexing, the prime at index five is 13.

**Theorem 1.4 (The prime at index six).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_six`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With zero-based indexing, the prime at index six is 17.

**Theorem 1.5 (The prime at index seven).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_seven`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With zero-based indexing, the prime at index seven is 19.

**Definition 1.6 (The first eight primes).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.firstEight`

*Formalization.* `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.firstEight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordered list is 2, 3, 5, 7, 11, 13, 17, 19. It supplies the rank bounds used in the radical estimate.

**Theorem 1.7 (Lower bounds at the first eight prime ranks).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.prime_rank_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.prime_rank_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a position i below eight in a finite sequence q, assume only that q is strictly increasing on the prefix through i and that the entries on this prefix are prime. Then q(i) is at least the i-th entry of the first-eight list. No condition is imposed on entries after i. The proof applies the general sorted-list prime bound to this finite prefix.

**Theorem 1.8 (Coordinatewise lower bounds for eight primes).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.first_eight_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.first_eight_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An increasing prime sequence of length eight dominates the first-eight list. This specialization supplies the initial eight factors in the radical estimate.

**Theorem 1.9 (A geometric radical lower bound).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.radical_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.radical_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a natural number n has at least 8+m distinct prime factors, then 9699690 times 19 to the power m is at most the product of its distinct prime factors. The first eight dominate the first-eight list, and every tail factor is at least 19. Arbitrary factor multiplicities are allowed.

**Theorem 1.10 (A reciprocal bound for the prime tail).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r be at least two and s at most six. A sequence q of length r+s needs to be strictly increasing and prime only on its first s+2 entries. Assume also that each suffix entry q(r+i) is at least q(i+2). Then the reciprocal suffix sum is bounded by the sum of reciprocals of the s entries starting at index two of the first-eight list. No other ordering or primality condition on the suffix is needed. The bound retains its dependence on s.

**Theorem 1.11 (Margin for at most five tail primes).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_margin_five`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_margin_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the prefix and suffix comparison assumptions of reciprocal_tail_bound, at most five tail primes leave 1 minus their reciprocal sum at least 36628/85085. This general bound is consumed by both threshold proofs; the fixed arithmetic checks occur inside its proof.

**Theorem 1.12 (Margin for six tail primes).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_margin_six`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_margin_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With six tail primes and the same prefix and suffix comparisons, 1 minus their reciprocal sum is at least 610847/1616615. The unbounded threshold argument uses this lower bound for its sieve margin.

## References

- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.firstEight`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.first_eight_le`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_five`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_le_get`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_seven`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_six`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_succ_le_of_prime`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.prime_rank_lower`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.radical_lower`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_bound`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_margin_five`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_margin_six`
