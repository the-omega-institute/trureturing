# Rational root change and local arithmetic of the native Thue cubic

## Abstract

A monic companion gives exact local readouts without changing the generated Thue field.

**Theorem 1.1 (The squared depressed root satisfies the monic equation).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange.monic_root`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange.monic_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After depressing the cubic, square the root and divide by the role prime. This gives the new monic cubic without choosing any roots of unity.

**Theorem 1.2 (The monic root generates the same simple field).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange.same_simple_field`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange.same_simple_field` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An explicit rational inverse recovers the original coordinate. The generated intermediate fields therefore agree exactly.

**Theorem 1.3 (Both affine charts have unit derivative modulo two).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange.binary_form_mod_two_chart_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange.binary_form_mod_two_chart_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Odd primary coordinates reduce the homogeneous form to the product of the three distinct projective linear factors over F₂. Either chart then gives a polynomial with derivative one.

**Theorem 1.4 (Exact valuation of the polynomial discriminant expression).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange.discriminant_arithmetic_depths`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange.discriminant_arithmetic_depths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the stated local-unit conditions, the polynomial discriminant expression has valuation two at the role prime and four at three. Field-discriminant and maximal-order claims are separate.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange.binary_form_mod_two_chart_derivative`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange.discriminant_arithmetic_depths`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange.monic_root`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange.same_simple_field`
