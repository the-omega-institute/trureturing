# Finite prime-count rows for the Robin reserve

## Abstract

Eight certified prime-count rows give the Robin reserve up to the Chebyshev cutoff.

Each row covers square cutoffs from A to 2A and counts primes in (2A, 3A] and (3A, 4A]. The two upper endpoints bound the reciprocal-square weights from below. The row inequalities give a common lower bound of 2/25 for the normalized prime band.

**Theorem 1.1 (Strict reserve through the finite cutoff).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveFiniteBand.neededReserve_lt_normalizedPrimeBand_of_sqrt_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveFiniteBand.neededReserve_lt_normalizedPrimeBand_of_sqrt_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real z at least 10000 with sqrt(2z) at most 25000, the normalized prime-band surplus strictly exceeds the Robin reserve.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveFiniteBand.neededReserve_lt_normalizedPrimeBand_of_sqrt_le`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus](EffectivePrimeSquareSurplus.md)
