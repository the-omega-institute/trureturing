# Binary Legendre squareclass certificates

## Abstract

Certificates of rational squareclass independence by actual finite Legendre signs.

**Theorem 1.1 (Injective Legendre sign columns rule out every nonempty rational-square product).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/FiniteLegendreSquareclassCertificate.not_isSquare_product_of_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/FiniteLegendreSquareclassCertificate.not_isSquare_product_of_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rational square of an integer is an integer square. After reducing at auxiliary primes its product sign is positive, so the selected subset would give a nonzero binary kernel vector.

**Theorem 1.2 (The certificate works directly for rational squareclasses).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/FiniteLegendreSquareclassCertificate.not_isSquare_rational_product_of_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/FiniteLegendreSquareclassCertificate.not_isSquare_rational_product_of_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying each input by the square of its denominator preserves the tested squareclass and gives an integer Legendre input.

**Theorem 1.3 (A binary matrix left inverse certifies injectivity).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/FiniteLegendreSquareclassCertificate.injective_mulVec_of_left_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/FiniteLegendreSquareclassCertificate.injective_mulVec_of_left_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite left inverse checked by matrix multiplication makes the sign oracle an independently verifiable certificate.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/FiniteLegendreSquareclassCertificate.injective_mulVec_of_left_inverse`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/FiniteLegendreSquareclassCertificate.not_isSquare_product_of_injective`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/FiniteLegendreSquareclassCertificate.not_isSquare_rational_product_of_injective`
