# Strict Divisor Chain Counts

## Abstract

Strict Divisor Chain Counts.

**Theorem 1.1 (The signed binomial counting formula).**

Lean statement: `D5/S3/Factorization/Combinatorics/StrictDivisorChainCount.strict_divisor_chain_count`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/StrictDivisorChainCount.strict_divisor_chain_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural endpoint n greater than one and for every length 1 ≤ k ≤ Ω(n), where Ω(n) counts prime factors with multiplicity, the number of strict divisor chains from one to n is the sum, over j from zero through k, of the weak counting function multiplied by binomial k choose j and the sign negative one to the power k minus j. The weak counting function is zero at length zero and otherwise is the product, over prime divisors p of n, of binomial a_p plus j minus one choose a_p, where a_p is the exponent of p in n. Successive quotients identify weak chains with positive factor tuples and strict chains with positive factor tuples whose entries are all different from one. Prime factorization identifies positive factor tuples with exponent compositions. Deleting prescribed unit factors gives the intersections used in finite inclusion-exclusion.

## References

- Truth anchor: `D5/S3/Factorization/Combinatorics/StrictDivisorChainCount.strict_divisor_chain_count`
