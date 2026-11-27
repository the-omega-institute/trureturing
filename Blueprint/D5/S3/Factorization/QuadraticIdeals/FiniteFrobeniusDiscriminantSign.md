# Finite matrix discriminant sign law

## Abstract

The exact finite-matrix distribution of the discriminant sign at fixed determinant.

**Theorem 1.1 (Shifted square character sum is minus one).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/FiniteFrobeniusDiscriminantSign.sum_character_shifted_square`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/FiniteFrobeniusDiscriminantSign.sum_character_shifted_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An explicit hyperbola factorization counts all square roots over the entire field by bijection with nonzero field elements.

**Theorem 1.2 (Exact zero-discriminant trace count).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/FiniteFrobeniusDiscriminantSign.discriminant_zero_card`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/FiniteFrobeniusDiscriminantSign.discriminant_zero_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cardinality of the trace values with zero discriminant is one plus the determinant quadratic character.

**Theorem 1.3 (Exact matrix-weighted sign moments).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/FiniteFrobeniusDiscriminantSign.discriminant_sign_moments`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/FiniteFrobeniusDiscriminantSign.discriminant_sign_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first and second moments use the true matrix trace fiber size at fixed determinant, not a uniform distribution on trace values.

**Theorem 1.4 (A nonsquare determinant yields an exactly fair sign bit).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/FiniteFrobeniusDiscriminantSign.nonsquare_det_sign_fair`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/FiniteFrobeniusDiscriminantSign.nonsquare_det_sign_fair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive and negative sign masses are each one half and no zero discriminants occur. This is a finite input for arithmetic independence tests, not a density theorem.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/FiniteFrobeniusDiscriminantSign.discriminant_sign_moments`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/FiniteFrobeniusDiscriminantSign.discriminant_zero_card`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/FiniteFrobeniusDiscriminantSign.nonsquare_det_sign_fair`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/FiniteFrobeniusDiscriminantSign.sum_character_shifted_square`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/FiniteTraceDeterminantMass](FiniteTraceDeterminantMass.md)
