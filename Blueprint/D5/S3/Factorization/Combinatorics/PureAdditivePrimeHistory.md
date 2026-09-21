# Pure Additive Prime Histories

## Abstract

Pure Additive Prime Histories.

**Theorem 1.1 (Additive evaluation).**

Lean statement: `D5/S3/Factorization/Combinatorics/PureAdditivePrimeHistory.pure_additive_run`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/PureAdditivePrimeHistory.pure_additive_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A word consisting only of additive prime letters adds the sum of its labels to any natural initial state. Starting at zero gives the prime sum itself; starting at one increases that endpoint by exactly one. The empty word leaves the initial state unchanged.

**Theorem 1.2 (Ordered tuple counts).**

Lean statement: `D5/S3/Factorization/Combinatorics/PureAdditivePrimeHistory.additive_tuple_count`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/PureAdditivePrimeHistory.additive_tuple_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An ordered tuple of k primes at most X gives a word by making every label an additive letter. Repeated primes are allowed, and the word uniquely determines the tuple. The words ending at the natural number N from initial state one therefore correspond bijectively to tuples with integer sum N minus one. This includes length zero and empty prime sets.

## References

- Truth anchor: `D5/S3/Factorization/Combinatorics/PureAdditivePrimeHistory.additive_tuple_count`
- Truth anchor: `D5/S3/Factorization/Combinatorics/PureAdditivePrimeHistory.pure_additive_run`
- Dependency: [D5/S3/Factorization/Combinatorics/MixedPrimeHistoryCount](MixedPrimeHistoryCount.md)
