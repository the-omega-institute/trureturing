# A Dyadic Analytic Integer Obstruction

## Abstract

A dyadic series cannot evaluate to a scaled integer beyond a quantitative tail threshold.

**Theorem 1.1 (Odd coefficient numerators prevent an integral value).**

Lean statement: `D5/S3/Arith/Primes/DyadicSeriesIntegerObstruction.dyadic_series_integer_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/DyadicSeriesIntegerObstruction.dyadic_series_integer_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r be a natural number at least one, x an integer greater than two, and s a complex sequence with s_0 = 1. Suppose the series of s_j times x^(-2j) sums to mu. Set e_j = j + v_2(j!). For every positive j, assume 2^e_j times s_j is an odd integer; this gives a lower bound on each such coefficient. Assume also that the absolute value of s_j is at most sqrt(2)^r times 4^j for every nonnegative j, and that x^2 - 4 > 128 times 6^r. Then the first omitted term dominates the remaining tail. Scaling the finite truncation by 2^e_J times x^(2J) gives an integer, with J the ceiling of r/2. The scaled analytic value differs from this integer by a nonzero quantity of modulus less than one. Since r is at most 2J, x^r times the analytic value cannot be an integer.

## References

- Truth anchor: `D5/S3/Arith/Primes/DyadicSeriesIntegerObstruction.dyadic_series_integer_obstruction`
