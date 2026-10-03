# Golden Cubic Block Native Power Periods

## Abstract

Golden cubic blocks have disjoint prime supports and exact native power periods.

**Theorem 1.1 (Disjoint supports and power periods).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockNativePowerPeriods.cubic_block_native_power_periods`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockNativePowerPeriods.cubic_block_native_power_periods` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C_j = |L_(3^j)^2 + 1| and B_j = |L_(3^j)^2 + 3|, where L is the golden Lucas sequence. Let pi(m) be the multiplicative order modulo m of the Fibonacci matrix with rows (1, 1) and (1, 0). For positive indices, distinct C blocks have coprime supports, distinct B blocks have coprime supports, and every C block is coprime to every B block. At each positive index j and positive exponents a and b, the Fibonacci matrix periods of C_j^a and B_j^b are respectively 4 times 3^(j+1) times C_j^(a-1) and 2 times 3^(j+1) times B_j^(b-1). The period of their product is 4 times 3^(j+1) times C_j^(a-1) times B_j^(b-1). Prime ranks separate the supports; the original Fibonacci valuations determine local prime-power periods, and CRT combines them.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockNativePowerPeriods.cubic_block_native_power_periods`
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockPrimePeriods](GoldenCubicBlockPrimePeriods.md)
- Dependency: [D5/S3/Arith/Primes/GoldenPrimePowerMatrixPeriod](GoldenPrimePowerMatrixPeriod.md)
