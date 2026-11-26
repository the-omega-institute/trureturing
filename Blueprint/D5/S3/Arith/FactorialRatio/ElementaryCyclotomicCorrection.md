# Cyclotomic factorial correction

## Abstract

The exact factorial and residue correction to the cyclotomic carry product.

**Definition 1.1 (Residue indicator).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.levelIndicator`

*Formalization.* `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.levelIndicator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The indicator is one at conductors r congruent to 1 modulo 4 for which the remainder of N modulo r reaches floor((r+2)/4). It is zero at every other level.

**Definition 1.2 (Prime-power deficit).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.levelDeficit`

*Formalization.* `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.levelDeficit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The deficit is the exceptional index count plus N at level two.

**Theorem 1.3 (Closed prime-power deficit count).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.levelDeficit_prime_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.levelDeficit_prime_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p and a positive exponent t, the count is the sum of the contribution N at p^t = 2, the floor N/p^t at odd p, and the residue indicator.

At r congruent to 1 modulo 4, exceptional indices are multiples of r. The last multiple is counted precisely when the remainder of N reaches the cutoff. At r congruent to 3 modulo 4, the first exceptional index is r minus the cutoff. The cutoff then brings each such index to a positive multiple of r. The two progression bijections hold for empty ranges as well.

**Definition 1.4 (Residual integer factor).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.RStar`

*Formalization.* `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.RStar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply p once for each selected prime power p^t up to 4N+1. Several selected powers of the same prime contribute separate copies of that prime.

**Theorem 1.5 (Exact factorial correction).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.EStar_eq_two_pow_digit_sum_mul_factorial_mul_RStar`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.EStar_eq_two_pow_digit_sum_mul_factorial_mul_RStar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exceptional factor equals 2 raised to the binary digit sum of N, times N factorial, times the residual factor.

Compare prime valuations. Legendre's factorial formula sums the odd level floors. At two, the exceptional valuation is N and the factorial valuation is N minus the binary digit sum.

**Definition 1.6 (Correction multinomial).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.correctionMultinomial`

*Formalization.* `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.correctionMultinomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the four parts N, N, N and N+1, divide the factorial of 4N+1 by the product of three copies of N factorial and one copy of (N+1) factorial.

**Theorem 1.7 (Residual factor divides the multinomial).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.RStar_dvd_correctionMultinomial`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.RStar_dvd_correctionMultinomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residual integer factor divides the correction multinomial for every N.

At each prime power, the multinomial valuation counts floors from its factorial quotient. After cancelling the quotient of N by the conductor, the floor difference depends only on the remainder. Each selected conductor contributes at least one to this difference.

**Theorem 1.8 (Linear logarithmic bound).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.log_RStar_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.log_RStar_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithm of the residual factor lies between zero and (4N+1) log 4.

Divisibility bounds the residual factor by the positive multinomial. The multinomial is one term in the expansion of four raised to 4N+1, obtained by raising the sum of four ones to that exponent.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.EStar_eq_two_pow_digit_sum_mul_factorial_mul_RStar`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.RStar`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.RStar_dvd_correctionMultinomial`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.correctionMultinomial`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.levelDeficit`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.levelDeficit_prime_pow`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.levelIndicator`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.log_RStar_bounds`
- Dependency: [D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd](ElementaryCyclotomicGcd.md)
