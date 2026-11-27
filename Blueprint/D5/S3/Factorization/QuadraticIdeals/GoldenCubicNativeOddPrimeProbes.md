# Exact small-prime Frobenius probes and the large-prime character inputs

## Abstract

Uniform native residual probes and arithmetic inputs for the odd-prime image criterion.

**Theorem 1.1 (Actual reductions give the split and nonsplit probes for 7, 11 and 13).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes.native_small_prime_certificates`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes.native_small_prime_certificates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four good-prime actual group counts yield both separable characteristic-polynomial types with exact companion scalar-power lengths: six and eight, five and twelve, or twelve or four and fourteen. This is finite arithmetic, not a full Galois image theorem.

**Theorem 1.2 (The good-prime seven trace does not vanish modulo any modulus above three).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes.native_trace7_nonzero_mod`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes.native_trace7_nonzero_mod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four native residues at seven give traces one, minus three, minus one, and three, whose reductions are nonzero for every modulus above three.

**Theorem 1.3 (Neither minus one nor minus two is a square at seven).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes.two_imaginary_characters_at_seven`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes.two_imaginary_characters_at_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact finite field exclusions are the quadratic-character arithmetic input at the uniform good prime.

**Theorem 1.4 (The j-offset has even valuation).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes.native_j_offset_even_valuation`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes.native_j_offset_even_valuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The j-invariant minus 1728 is the square of twenty-four times the native Lucas coordinate. Its valuation is twice the corresponding rational valuation.

**Theorem 1.5 (The two-adic valuation of the native j-invariant is exactly six).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes.native_j_two_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes.native_j_two_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Lucas coordinate is even, so the native block is odd. The remaining coefficient 576 is sixty-four times nine.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes.native_j_offset_even_valuation`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes.native_j_two_exact`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes.native_small_prime_certificates`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes.native_trace7_nonzero_mod`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes.two_imaginary_characters_at_seven`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFiveProbes](GoldenCubicNativeFiveProbes.md)
