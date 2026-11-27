# Maximal order and field discriminant of the native Thue cubic

## Abstract

The marked cubic admits an explicit maximal integral lattice and signed field discriminant 81P squared.

**Theorem 1.1 (The four marked generators span the full integral closure).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueMaximalOrder.native_maximal_span`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueMaximalOrder.native_maximal_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scaled root basis has trace determinant 81P to the fourth. Add the monic companion and use its two Eisenstein certificates to cancel the only denominator primes globally. The result is an equality of actual integer submodules, not a polynomial discriminant.

**Theorem 1.2 (The exact signed field discriminant is 81P squared).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueMaximalOrder.native_field_discriminant`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueMaximalOrder.native_field_discriminant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the third integral generator to be (beta + k alpha + l)/P with A k congruent to D and A l congruent to D squared modulo P. The same lattice is obtained for every such pair. Its trace determinant is the signed number-field discriminant. This does not by itself exclude the original two-prime factorization.

**Theorem 1.3 (The original Lucas factorization supplies the marked field and its integral basis).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueMaximalOrder.actual_factorization_field_discriminant`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueMaximalOrder.actual_factorization_field_discriminant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original Lucas block equation itself supplies the oriented square-role ideal, the actual Thue splitting field, and all unit conditions. Its field discriminant is 81P squared, and the explicit three vectors span its integral closure. The original nonexistence claim is still open.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueMaximalOrder.actual_factorization_field_discriminant`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueMaximalOrder.native_field_discriminant`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueMaximalOrder.native_maximal_span`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/CubicIntegralLattice](CubicIntegralLattice.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueEisenstein](GoldenCubicThueEisenstein.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange](GoldenCubicThueRootChange.md)
