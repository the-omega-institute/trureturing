# Diagonal Sign Inertia

## Abstract

The inertia of a real diagonal Hermitian form is exactly its coordinate sign count.

**Definition 1.1 (Real diagonal Hermitian form).**

Lean statement: `D5/S3/Weil/Pick/DiagonalSignNegativeIndex.realDiagonal`

*Formalization.* `D5/S3/Weil/Pick/DiagonalSignNegativeIndex.realDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Real coefficients are embedded as the diagonal entries of a complex Hermitian matrix.

**Definition 1.2 (Positive coordinate count).**

Lean statement: `D5/S3/Weil/Pick/DiagonalSignNegativeIndex.positiveWeightCount`

*Formalization.* `D5/S3/Weil/Pick/DiagonalSignNegativeIndex.positiveWeightCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This finite count records diagonal entries that are strictly positive.

**Definition 1.3 (Negative coordinate count).**

Lean statement: `D5/S3/Weil/Pick/DiagonalSignNegativeIndex.negativeWeightCount`

*Formalization.* `D5/S3/Weil/Pick/DiagonalSignNegativeIndex.negativeWeightCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This finite count records diagonal entries that are strictly negative.

**Theorem 1.4 (Diagonal inertia equals coordinate sign counts).**

Lean statement: `D5/S3/Weil/Pick/DiagonalSignNegativeIndex.real_diagonal_inertia_eq_sign_counts`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/DiagonalSignNegativeIndex.real_diagonal_inertia_eq_sign_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinate projectors give lower bounds for both signs, and the rank partition forces both bounds to be equalities.

**Theorem 1.5 (Diagonal negative index counts negative weights).**

Lean statement: `D5/S3/Weil/Pick/DiagonalSignNegativeIndex.real_diagonal_negIndex_eq_negative_count`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/DiagonalSignNegativeIndex.real_diagonal_negIndex_eq_negative_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative component of the inertia package is exposed as a direct consumer theorem.

## References

- Truth anchor: `D5/S3/Weil/Pick/DiagonalSignNegativeIndex.realDiagonal`
- Truth anchor: `D5/S3/Weil/Pick/DiagonalSignNegativeIndex.positiveWeightCount`
- Truth anchor: `D5/S3/Weil/Pick/DiagonalSignNegativeIndex.negativeWeightCount`
- Truth anchor: `D5/S3/Weil/Pick/DiagonalSignNegativeIndex.real_diagonal_inertia_eq_sign_counts`
- Truth anchor: `D5/S3/Weil/Pick/DiagonalSignNegativeIndex.real_diagonal_negIndex_eq_negative_count`
