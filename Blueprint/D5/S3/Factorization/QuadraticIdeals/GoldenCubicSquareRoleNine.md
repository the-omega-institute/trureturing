# Exact modulo-nine coordinates of the square-role Eisenstein factor

## Abstract

The original square-times-cube Lucas block forces exact congruences on its square prime.

**Theorem 1.1 (The primary square coordinates are forced).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicSquareRoleNine.primary_square_coordinates_nine`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicSquareRoleNine.primary_square_coordinates_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cube of a primary element is one modulo nine. Thus the original product fixes both coordinates of the primary square factor.

**Theorem 1.2 (The proposed native factorization forces an oriented norm representation).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicSquareRoleNine.actual_square_role_coordinates_nine`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicSquareRoleNine.actual_square_role_coordinates_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the square-root-minus-three basis the two integral coordinates must be four and eight modulo nine, respectively. The witness divides the actual oriented Lucas element. The argument uses the native primary prime-ideal product, rather than assuming a proposed coordinate tuple.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicSquareRoleNine.actual_square_role_coordinates_nine`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicSquareRoleNine.primary_square_coordinates_nine`
- Dependency: [D5/S1/Scale/GoldenCubicBlockCongruences](../../../S1/Scale/GoldenCubicBlockCongruences.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/GoldenCubicPrimaryProduct](GoldenCubicPrimaryProduct.md)
