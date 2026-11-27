# Exact lag valuations and periods of cubic Lucas blocks

## Abstract

Exact valuations of differences between later Lucas blocks determine their congruence periods.

**Theorem 1.1 (Leading term at two odd strides).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockLagValuation.native_block_leading`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockLagValuation.native_block_leading` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an odd Lucas seed and two odd strides, factor the difference of the squared traces using both the sum and the difference of the strides. Binomial lifting in the native golden integer ring identifies the leading residue in the ordinary integer difference. The identity does not require choosing a split p-adic root.

**Theorem 1.2 (Exact valuation at every later lag).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockLagValuation.golden_cubic_tail_clock_valuation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockLagValuation.golden_cubic_tail_clock_valuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p divide the earlier cubic block B_i, and let h be its valuation there. For the later sequence starting with B_(i+1), the valuation of the difference at positive lag d is 2h plus the valuation of 9^d minus one. No assertion about which blocks have an exponent-one factor is implied.

**Theorem 1.3 (All periods at every higher precision).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockLagValuation.golden_cubic_tail_period`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockLagValuation.golden_cubic_tail_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At modulus p^(2h+r), a lag is a period of the later blocks exactly when the same power of nine returns to one modulo p^r. The onset of distinguishable residues is controlled by the earlier block depth; the resulting period is a separate multiplicative condition.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockLagValuation.golden_cubic_tail_clock_valuation`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockLagValuation.golden_cubic_tail_period`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockLagValuation.native_block_leading`
- Dependency: [D5/S1/Scale/GoldenCubicBlockCongruences](../../../S1/Scale/GoldenCubicBlockCongruences.md)
