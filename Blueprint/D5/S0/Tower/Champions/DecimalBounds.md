# Certified Decimal Bounds

## Abstract

Four exact frozen constants certify the six-place decimals quoted by the source.

**Theorem 1.1 (Tribonacci Perron-root decimal).**

$$\left|t - \frac{1839287}{1000000}\right| < \frac{1}{2000000}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/DecimalBounds.tribonacci_constant_rounding_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The characteristic polynomial is negative at 1.8392865 and positive at 1.8392875. The intermediate root is the frozen Perron root by its exact uniqueness theorem, certifying 1.839287.

**Theorem 1.2 (Shifted Tribonacci Binet-coefficient decimal).**

$$\left|a \cdot t - \frac{618420}{1000000}\right| < \frac{1}{2000000}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/DecimalBounds.tribonacci_shifted_binet_coefficient_rounding_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here a times t is exactly the source normalization a prime, as fixed by the normalization bridge. Rational endpoint comparisons certify the decimal 0.618420.

**Theorem 1.3 (Zeckendorf coding-fingerprint decimal).**

$$\left|\mathit{rZeckendorf} - \frac{1170820}{1000000}\right| < \frac{1}{2000000}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/DecimalBounds.zeckendorf_coding_fingerprint_rounding_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen exact value phi squared over square root five, together with exact rational square bounds for square root five, certifies the decimal 1.170820.

**Theorem 1.4 (Tribonacci coding-fingerprint decimal).**

$$\left|\mathit{rTribonacci} - \frac{2092100}{1000000}\right| < \frac{1}{2000000}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/DecimalBounds.tribonacci_coding_fingerprint_rounding_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalization bridge reduces the fingerprint to a rational function of t. A tighter cubic sign bracket from 1.83928675 to 1.83928676 certifies the decimal 2.092100.

## References

- Truth anchor: `D5/S0/Tower/Champions/DecimalBounds.tribonacci_coding_fingerprint_rounding_bound`
- Truth anchor: `D5/S0/Tower/Champions/DecimalBounds.tribonacci_constant_rounding_bound`
- Truth anchor: `D5/S0/Tower/Champions/DecimalBounds.tribonacci_shifted_binet_coefficient_rounding_bound`
- Truth anchor: `D5/S0/Tower/Champions/DecimalBounds.zeckendorf_coding_fingerprint_rounding_bound`
- Dependency: [D5/S0/Tower/Champions/CodingFingerprint](CodingFingerprint.md)
