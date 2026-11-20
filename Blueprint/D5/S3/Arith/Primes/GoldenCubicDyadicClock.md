# Exact dyadic clock of cubic Lucas blocks

## Abstract

The positive-index cubic Lucas blocks fill a single residue class modulo 128, with exact periods at every dyadic precision.

**Theorem 1.1 (Native exact dyadic lag).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicDyadicClock.golden_cubic_dyadic_lag`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicDyadicClock.golden_cubic_dyadic_lag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For B_n equal to the squared Lucas trace at index 3^n plus three, and n greater than m at least one, the valuation of B_n minus B_m is seven plus the valuation of n minus m. The proof squares an integer iterate whose displacement is odd after extracting the claimed power of two, then sums the increments for the odd part of the lag.

**Theorem 1.2 (Least period at every dyadic precision).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicDyadicClock.dyadicBlock_least_period`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicDyadicClock.dyadicBlock_least_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Modulo 2^a, the least positive period of the positive-index sequence is one through precision seven and 2^(a-7) thereafter.

**Theorem 1.3 (Each residue is visited exactly once per cycle).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicDyadicClock.dyadicBlock_one_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicDyadicClock.dyadicBlock_one_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At precision 7+k, every residue equal to 19 modulo 128 occurs at a unique index in the first 2^k positive-index blocks. No odd prime divisor or choice of p-adic root is needed.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicDyadicClock.dyadicBlock_least_period`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicDyadicClock.dyadicBlock_one_cycle`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicDyadicClock.golden_cubic_dyadic_lag`
- Dependency: [D5/S1/Scale/GoldenCubicBlockCongruences](../../../S1/Scale/GoldenCubicBlockCongruences.md)
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage](GoldenCubicBlockTailOrbitImage.md)
