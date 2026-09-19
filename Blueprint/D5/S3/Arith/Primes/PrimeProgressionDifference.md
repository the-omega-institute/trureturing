# The common difference of a progression of primes

## Abstract

An arithmetic progression of primes at least as long as a prime p either has p dividing its common difference or has p among its terms.

A progression whose common difference is invertible modulo a prime p visits every residue class modulo p within its first p terms, so one of those terms is divisible by p. If the terms are prime, such a term can only be p itself. That is the whole mechanism, and it is what makes long progressions of primes force highly divisible differences.

**Theorem 1.1 (The dichotomy).**

Lean statement: `D5/S3/Arith/Primes/PrimeProgressionDifference.prime_dvd_difference_or_eq_term`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/PrimeProgressionDifference.prime_dvd_difference_or_eq_term` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a, d and L be naturals with the term at index i prime for every i below L, and let p be a prime at most L. Then p divides d, or some index below L has its term equal to p. When p does not divide d, the residue of d modulo p is invertible, so the natural representative below p of the negative of a times that inverse is an index at which the term vanishes modulo p. That index is below p and hence below L, so its term is prime and divisible by p, which forces it to equal p. Positivity of d is not needed: when d is zero the first alternative holds outright.

**Theorem 1.2 (When the progression starts above its length).**

Lean statement: `D5/S3/Arith/Primes/PrimeProgressionDifference.prime_dvd_difference_of_length_lt_start`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/PrimeProgressionDifference.prime_dvd_difference_of_length_lt_start` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If in addition the length L is smaller than the initial term a, then every prime at most L divides d. The second alternative of the dichotomy is impossible here, because a term is at least a, which exceeds L, which in turn is at least p.

## References

- Truth anchor: `D5/S3/Arith/Primes/PrimeProgressionDifference.prime_dvd_difference_of_length_lt_start`
- Truth anchor: `D5/S3/Arith/Primes/PrimeProgressionDifference.prime_dvd_difference_or_eq_term`
