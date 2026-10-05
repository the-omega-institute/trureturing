# Shifted Quadratic Character Sum over a Finite Field

## Abstract

For an odd finite field, the quadratic character of a nonsingular shifted square has total sum `-1`.

**Theorem 1.1 (Shifted quadratic character sum).**  If `F` is a finite field of odd characteristic and `a ∈ F` is nonzero, then

$$\sum_{x\in F}\chi_F(x^2-a)=-1,$$

where `χ_F` is the quadratic character.

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FiniteFieldQuadraticCharacterSum.quadraticChar_shift_square_sum` (`✓ std3`). ∎

*Source.* Lidl–Niederreiter, *Finite Fields*, 2nd ed. (1997), character-sum chapter.

*Commentary.*

The proof counts the points on `y² = x² − a`. The odd-characteristic change of variables `u = x − y`, `v = x + y` identifies this conic with `uv = a`; since `a ≠ 0`, the latter has one point for each nonzero `u`, hence `|F| − 1` points. `quadraticChar_card_sqrts` converts the fibre count back to the character sum.

The hypotheses are material: characteristic two makes the linear change singular, and `a = 0` is the singular case with a different sum.

## References

- Truth anchor: `D5/S3/Arith/FiniteFieldQuadraticCharacterSum.quadraticChar_shift_square_sum`
- Helper: `D5/S3/Arith/FiniteFieldQuadraticCharacterSum.conic_card_eq_card_field_sub_one`
- Lidl–Niederreiter, *Finite Fields*, 2nd ed., Cambridge University Press, 1997.
