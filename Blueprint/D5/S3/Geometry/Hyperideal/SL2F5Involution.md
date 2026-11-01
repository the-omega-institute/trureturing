# The SL2(F5) square-one classification

## Abstract

Square-one determinant-one matrices over the field with five elements are only the two central signs.

For every determinant-one two by two matrix over ZMod 5, if its square is the identity, then the matrix is either the identity or its negative. This is the finite-field calculation used by the center-lift obstruction: a nontrivial projective involution cannot lift to a square-one element.

Let q be the canonical quotient homomorphism from SL2(F5) to PSL2(F5), obtained by quotienting by the center. For any Y in SL2(F5), assume q(Y) squared is the identity and q(Y) is not the identity. Then Y squared is negative identity, Y to the fourth power is identity, and the order of Y is exactly four.

The projective square condition puts Y squared in the center. A central determinant-one matrix in dimension two is scalar, and its scalar r satisfies r squared equals one; over F5 this gives r equal to one or negative one. If Y squared were identity, the square-one classification would force Y itself to be identity or negative identity, and either choice has trivial projective image. Thus Y squared is negative identity. Squaring once more gives Y to the fourth power equal to identity; since Y squared is not identity, its order is four.

This consequence quantifies over every lift Y of every nontrivial projective involution. The argument uses the canonical central quotient uniformly over all lift choices. To infer the CFMP edge-degree change, one must additionally establish the correspondence between a three-step return and an actual edge fiber.

**Theorem 1.1 (Square-one classification in SL2(F5)).**

Lean statement: `D5/S3/Geometry/Hyperideal/SL2F5Involution.sl2_zmod5_square_one_eq_one_or_neg_one`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SL2F5Involution.sl2_zmod5_square_one_eq_one_or_neg_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every A in the determinant-one two by two matrices over ZMod 5 with A squared equal to the identity is either the identity matrix or the negative identity matrix.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/SL2F5Involution.sl2_zmod5_square_one_eq_one_or_neg_one`
