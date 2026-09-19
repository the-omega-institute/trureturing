# Sign-safe squares and norm squares

## Abstract

Sign-safe squares and norm squares.

**Theorem 1.1 (Checked square expressions).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/SignedSquares.square_factory_correct`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/SignedSquares.square_factory_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every accepted annotated rational expression, squareBounds chooses the correct lower square endpoint on positive or negative intervals and zero on intervals crossing zero. Its upper endpoint is the maximum of the two endpoint squares. The resulting square expression passes the checker and encloses the real square.

**Theorem 1.2 (Square width on a bounded interval).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/SignedSquares.square_bounds_width_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/SignedSquares.square_bounds_width_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For -A<=l<=u<=A with A nonnegative, the square bounds are nonnegative and ordered, their upper endpoint is at most A^2, and their width is at most 2A(u-l).

**Theorem 1.3 (Two signed differences).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/SignedSquares.norm_sq_difference_width_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/SignedSquares.norm_sq_difference_width_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two pairs of ordered intervals in [-Ap,Ap] and [-Aq,Aq], subtracting opposite endpoints and summing the two square intervals gives an ordered nonnegative norm-square interval. Its upper endpoint is at most (2Ap)^2+(2Aq)^2, and its width is bounded by four times each amplitude times the sum of the corresponding two input widths.

## References

- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/SignedSquares.norm_sq_difference_width_le`
- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/SignedSquares.square_bounds_width_le`
- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/SignedSquares.square_factory_correct`
- Dependency: [D5/S0/Certificates/BoxCover/RationalIntervalExpression](../../../../S0/Certificates/BoxCover/RationalIntervalExpression.md)
