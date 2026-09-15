# Strict Divisor Chains and the Möbius Function

## Abstract

Strict Divisor Chains and the Möbius Function.

**Theorem 1.1 (The alternating chain formula).**

Lean statement: `D5/S3/Factorization/Combinatorics/StrictDivisorChainMobius.chain_alternating_sum_eq_moebius`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/StrictDivisorChainMobius.chain_alternating_sum_eq_moebius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive integer n, the alternating sum of the numbers of strict divisor chains from one to n equals the Möbius function at n. The sum includes lengths from zero through Ω(n), the number of prime factors with multiplicity. Removing the last step partitions nonempty chains by their penultimate proper divisor. Strict chains have length at most Ω(n), so this partition gives the divisor recursion for the alternating sum. At n = 1 the unique empty chain contributes one. These initial and recursive values determine the Möbius function.

## References

- Truth anchor: `D5/S3/Factorization/Combinatorics/StrictDivisorChainMobius.chain_alternating_sum_eq_moebius`
- Dependency: [D5/S3/Factorization/Combinatorics/StrictDivisorChainCount](StrictDivisorChainCount.md)
