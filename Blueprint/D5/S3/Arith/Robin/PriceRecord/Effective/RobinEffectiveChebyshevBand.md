# The Robin prime-band reserve from Chebyshev estimates

## Abstract

Elementary Chebyshev estimates and the finite prime counts give the strict Robin reserve.

At square cutoff a = sqrt(2z) at least 25000, use the intervals (a, 4a], (4a, 8a] and (8a, 16a]. The Chebyshev estimates give a lower bound of 19/(160a) for the sum of log(p)/p^2 over these primes. Normalizing the actual Robin weights gives a lower bound of 931/16000 for the prime band.

**Theorem 1.1 (Strict reserve above the Chebyshev cutoff).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveChebyshevBand.neededReserve_lt_normalizedPrimeBand_of_sqrt_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveChebyshevBand.neededReserve_lt_normalizedPrimeBand_of_sqrt_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real z at least 10000 with sqrt(2z) at least 25000, the normalized prime-band surplus strictly exceeds the Robin reserve.

**Theorem 1.2 (Strict reserve for all large cutoffs).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveChebyshevBand.neededReserve_lt_normalizedPrimeBand`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveChebyshevBand.neededReserve_lt_normalizedPrimeBand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real z at least 10000, the normalized prime-band surplus strictly exceeds the Robin reserve.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveChebyshevBand.neededReserve_lt_normalizedPrimeBand`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveChebyshevBand.neededReserve_lt_normalizedPrimeBand_of_sqrt_ge`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus](EffectivePrimeSquareSurplus.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveFiniteBand](RobinEffectiveFiniteBand.md)
