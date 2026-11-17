# Original minus-identity rows

## Abstract

For prime p, X≤Y and 6Y<p², literal ordered integer-box minus-identity solutions satisfy Nminus≤3Uminus+8(2Y+1)² for the same fixed alternating units. The proof keeps zero rows, nonunit rows, repeated endpoints and all-six-divisible tuples. It first proves the exact four-equation equivalence for the existing sixReturnWord, derives all minors, and covers nonvanishing rows by three even cyclic rotations. A nonzero p-divisible row is encoded by two entries divided by p and one opposite pivot coordinate; the exactly zero row is encoded by two opposite entries. No row-count supplier is assumed. The lower bound p≤X is unnecessary. This is the all-strata reduction for the minus center, not the full original estimate.

For prime p, X≤Y and 6Y<p², literal ordered integer-box minus-identity solutions satisfy Nminus≤3Uminus+8(2Y+1)² for the same fixed alternating units. The proof keeps zero rows, nonunit rows, repeated endpoints and all-six-divisible tuples. It first proves the exact four-equation equivalence for the existing sixReturnWord, derives all minors, and covers nonvanishing rows by three even cyclic rotations. A nonzero p-divisible row is encoded by two entries divided by p and one opposite pivot coordinate; the exactly zero row is encoded by two opposite entries. No row-count supplier is assumed. The lower bound p≤X is unnecessary. This is the all-strata reduction for the minus center, not the full original estimate.

**Definition 1.1 (MinusEquations).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.MinusEquations`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiMinusRows.MinusEquations` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The four equations in the original six letters, with no entry inverted.

**Theorem 1.2 (sixReturnWord_minus_iff).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.sixReturnWord_minus_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiMinusRows.sixReturnWord_minus_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Exact equivalence for the existing alternating transfer word, including zero entries.

**Theorem 1.3 (MinusEquations.third_minor).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.third_minor`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiMinusRows.third_minor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The third minor follows without cancelling any original coordinate.

**Theorem 1.4 (MinusEquations.even_rotate).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.even_rotate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiMinusRows.even_rotate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Even cyclic rotation preserves the fixed alternating coefficients.

**Definition 1.5 (ReturnRows).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.ReturnRows`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiMinusRows.ReturnRows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Original integer letters grouped as the two rows (a,b,w) and (d,v,t).

**Definition 1.6 (literalRowBox).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.literalRowBox`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiMinusRows.literalRowBox` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The literal, independently bounded integer rows.

**Definition 1.7 (minusSolutions).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.minusSolutions`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiMinusRows.minusSolutions` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Actual minus-identity returns of the existing six-letter word.

**Definition 1.8 (Nminus).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.Nminus`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiMinusRows.Nminus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The original literal-box minus-identity count.

**Definition 1.9 (Uminus).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.Uminus`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiMinusRows.Uminus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The same original solutions, with the middle column consisting of units mod p.

**Definition 1.10 (RowEquations).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.RowEquations`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiMinusRows.RowEquations` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Coordinate-free row equations; all three minors are retained.

**Theorem 1.11 (MinusEquations.rows).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.rows`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiMinusRows.rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The original four equations supply every minor, also at composite moduli.

**Theorem 1.12 (row_zero_sum).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.row_zero_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiMinusRows.row_zero_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

A row divisible by p has exact integer sum zero in the short prime-cube box.

**Definition 1.13 (rowSolutions).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.rowSolutions`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiMinusRows.rowSolutions` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The actual finite row-equation solution set, before any strata are removed.

**Theorem 1.14 (divisible_row_count).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.divisible_row_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiMinusRows.divisible_row_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Divisible rows, including the exactly zero row, have a genuine finite bound.

**Theorem 1.15 (divisible_row_count_square).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.divisible_row_count_square`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiMinusRows.divisible_row_count_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Every p-divisible first row costs at most four square interval lengths. This bound covers all-six-divisible tuples and every exact zero without removing any stratum.

**Theorem 1.16 (RowEquations.unit_column).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.unit_column`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiMinusRows.unit_column` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Rank at most one modulo p, with a common unit column whenever neither row vanishes.

**Theorem 1.17 (RowEquations.transpose_rows).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.transpose_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiMinusRows.transpose_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

All row minors and the equations are symmetric under exchanging the two rows.

**Theorem 1.18 (RowEquations.cycle_columns).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.cycle_columns`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiMinusRows.cycle_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Simultaneously cyclically permuting columns preserves the original row equations.

**Definition 1.19 (rotateRows).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.rotateRows`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiMinusRows.rotateRows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Even cyclic rotation on the original literal integer six-tuples.

**Theorem 1.20 (rowSolutions_count_reduction).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.rowSolutions_count_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiMinusRows.rowSolutions_count_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

All strata are paid for by the three cyclic unit-middle charts and eight square interval lengths. The finite set contains the original integer coordinates.

**Theorem 1.21 (minusSolutions_eq_rowSolutions).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.minusSolutions_eq_rowSolutions`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiMinusRows.minusSolutions_eq_rowSolutions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Exact identification of the polynomial row set with the original word solutions.

**Theorem 1.22 (Nminus_le_three_Uminus).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMinusRows.Nminus_le_three_Uminus`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiMinusRows.Nminus_le_three_Uminus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Original prime-cube nonunit-row reduction, for the literal integer box and the same fixed alternating units. No row-count or coefficient-realization supplier occurs.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.MinusEquations`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.Nminus`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.Nminus_le_three_Uminus`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.ReturnRows`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.RowEquations`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.Uminus`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.cycle_columns`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.divisible_row_count`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.divisible_row_count_square`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.even_rotate`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.literalRowBox`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.minusSolutions`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.minusSolutions_eq_rowSolutions`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.rotateRows`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.rowSolutions`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.rowSolutions_count_reduction`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.row_zero_sum`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.rows`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.sixReturnWord_minus_iff`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.third_minor`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.transpose_rows`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMinusRows.unit_column`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiSixWordFiber](PascadiSixWordFiber.md)
