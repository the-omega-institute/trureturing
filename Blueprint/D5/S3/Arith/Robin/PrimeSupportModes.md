# Five Prime-Support Modes for the Robin Reduction

## Abstract

Every natural number belongs to one of five distinct-prime support strata, and the two-through-eight stratum is already covered by the Robin theorem.

**Theorem 1.1 (Exhaustive support classification).**

$$\forall n \in \mathbb{N},\; card\left(primeFactors\left(n\right)\right) = 0 \lor \left(card\left(primeFactors\left(n\right)\right) = 1 \lor \left(\left(2 \le card\left(primeFactors\left(n\right)\right) \land card\left(primeFactors\left(n\right)\right) \le 8\right) \lor \left(\left(9 \le card\left(primeFactors\left(n\right)\right) \land card\left(primeFactors\left(n\right)\right) \le 11\right) \lor 12 \le card\left(primeFactors\left(n\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PrimeSupportModes.primeSupportMode_cases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The five bins are empty support, singleton support, two through eight distinct primes, nine through eleven distinct primes, and at least twelve distinct primes.

The two-through-eight bin reuses the existing formal Robin theorem above 5040. The remaining bins stay explicit interfaces for the Euler-layer and clock arguments; a strict failure above 5040 is therefore forced into the nine-through-eleven or twelve-plus bin. This document does not claim the full Robin theorem.

For the 5040 congruence shape, a residual with at most five distinct primes gives at most nine total support primes. The theorem modEq_2241_card_le_nine_of_residual_card_le_five records this support bound; combined with robin_failure_mode, robin_failure_residual_card_eq_five forces every failing five-prime residual to use all five residual primes and total support exactly nine. The bridge robin_failure_modEq_2241_residual_card_le_five consumes the literal 5040 divisibility and congruence premises.

## References

- Truth anchor: `D5/S3/Arith/Robin/PrimeSupportModes.primeSupportMode_cases`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenCell5040Shape](../GoldenResource/GoldenCell5040Shape.md)
- Dependency: [D5/S3/Arith/Robin/FewDistinctPrimes](FewDistinctPrimes.md)
