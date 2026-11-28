# Native Frobenius squareclass independence at 97

## Abstract

Five actual native Frobenius squareclasses are independent at the common good prime 97.

**Theorem 1.1 (The observed prime is nonsquare in every auxiliary row).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97.at97_auxiliary_nonsquare`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97.at97_auxiliary_nonsquare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prime 97 has character -1 at 5, 7, 13, 19 and 29. These are the rows of the binary certificate.

**Theorem 1.2 (Five actual good-reduction point counts at 97).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97.native_at97_good_count`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97.native_at97_good_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All five curves are smooth modulo 97. Their group carriers have 88, 101, 103, 107 and 100 points, including infinity.

**Theorem 1.3 (Frobenius discriminants computed from those native point counts).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97.nativeDiscriminant97_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97.nativeDiscriminant97_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace discriminants are -288, -379, -363, -307 and -384; they are not the Weierstrass discriminants.

**Theorem 1.4 (Five native Frobenius squareclasses are independent over the rationals).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97.native_at97_not_isSquare_product`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97.native_at97_not_isSquare_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonempty finite subset has nonsquare product. The five-row Legendre matrix and its checked binary left inverse certify this one-prime result, not a general density or lifting theorem.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97.at97_auxiliary_nonsquare`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97.nativeDiscriminant97_eq`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97.native_at97_good_count`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97.native_at97_not_isSquare_product`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/FiniteLegendreSquareclassCertificate](FiniteLegendreSquareclassCertificate.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFiveProbes](GoldenCubicNativeFiveProbes.md)
