# Shifted Quadratic Character Sum over a Finite Field

## Abstract

The shifted quadratic character sum over an odd finite field is -1 away from the singular parameter.

**Theorem 1.1 (The shifted quadratic character sum is minus one).**

$$\forall F, a, ringChar(F)\neq2 \land a\neq0 \Rightarrow \sum_{x\in F} \operatorname{quadraticChar}(F)(x^{2}-a)=-1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FiniteFieldQuadraticCharacterSum.quadraticChar_shift_square_sum` (`✓ std3`). ∎

*Citation.* Rudolf Lidl; Harald Niederreiter (1997). *Finite Fields*. URL: <https://doi.org/10.1017/CBO9780511525790>.

*Commentary.*

For a finite field of odd characteristic and a nonzero shift a, the quadratic character of x squared minus a sums to minus one over all x. The proof counts the conic y squared equals x squared minus a.

The change of variables u equals x minus y and v equals x plus y is invertible exactly because the characteristic is not two. The equation becomes uv equals a, which has one point for every nonzero u. The hypothesis a nonzero excludes the singular boundary.

**Theorem 1.2 (The shifted-square conic has q minus one points).**

$$\forall F, a, ringChar(F)\neq2 \land a\neq0 \Rightarrow \operatorname{card}(\operatorname{Conic}(F, a))=card(F)-1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FiniteFieldQuadraticCharacterSum.conic_card_eq_card_field_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This helper is the finite point-counting statement used by the character-sum theorem. Its proof factors the conic through the hyperbola uv equals a and then through the nonzero elements of F.

## References

- Truth anchor: `D5/S3/Arith/FiniteFieldQuadraticCharacterSum.conic_card_eq_card_field_sub_one`
- Truth anchor: `D5/S3/Arith/FiniteFieldQuadraticCharacterSum.quadraticChar_shift_square_sum`
- Dependency: [D5/S3/ArithUnits/FiniteFieldTwoSquares](../ArithUnits/FiniteFieldTwoSquares.md)
