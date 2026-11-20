# The exact cube-stripped elliptic twist

## Abstract

An exact cubic-block quadratic twist removes the cube factor from the discriminant.

**Theorem 1.1 (The twist and scaling remove the cubic part from the short model).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicCubeStrippedTwist.is_twist_stripped`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicCubeStrippedTwist.is_twist_stripped` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Writing the block as C cubed times R, the C-twist followed by the admissible scaling with unit C has coefficients minus three C R and two R L.

**Theorem 1.2 (The hypothetical square-cube case has good reduction at the cube prime after twisting).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicCubeStrippedTwist.square_cube_twist_good_at_cube_prime`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicCubeStrippedTwist.square_cube_twist_good_at_cube_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stripped discriminant is the square of seventy-two times the square-role factor squared, hence nonzero at the distinct cube-role prime above three. This conditional model change does not exclude that factorization.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicCubeStrippedTwist.is_twist_stripped`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicCubeStrippedTwist.square_cube_twist_good_at_cube_prime`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic](GoldenCubicNativeElliptic.md)
