# One-defect king colourings: KingHorizontal

## Abstract

Finite colourings with exactly one monochromatic king bond.

**Theorem 1.1 (Horizontal defects in two rows).**

$$\forall (M: \operatorname{Nat}), (\operatorname{KingDifference}.\operatorname{N_{H}}\left(1, M\right) = (6) \cdot ((M) \cdot ((2)^{M})))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.horizontal_two_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The natural count is six times the number of positions times a binary-word count.

**Theorem 1.2 (Horizontal defects in two columns).**

$$\forall (p: \operatorname{Nat}), (\operatorname{KingDifference}.\operatorname{N_{H}}\left((p) + (1), 1\right) = (6) \cdot ((((3) \cdot (p)) + (2)) \cdot ((2)^{p})))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.horizontal_two_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The natural formula separates the boundary rows from the interior rows.

**Theorem 1.3 (Horizontal defects in three rows).**

$$\forall (q: \operatorname{Nat}), ((\operatorname{KingDifference}.\operatorname{N_{H}}\left(2, (q) + (1)\right)) + (54) = (6) \cdot ((((q) + (13)) \cdot ((2)^{q})) + ((3) \cdot ((q) + (2)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.horizontal_three_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The additive form keeps every operation in the natural numbers.

**Theorem 1.4 (The general horizontal orientation sum).**

$$\forall (t: \operatorname{Nat}), (\forall (q: \operatorname{Nat}), ((\operatorname{KingDifference}.\operatorname{N_{H}}\left((t) + (3), (q) + (2)\right)) + ((6) \cdot (((8) \cdot ((t) + (4))) + (4))) = (6) \cdot ((((((t) + (4)) \cdot ((q) + (2))) + (8)) \cdot ((2)^{(t) + (2)})) + ((((3) \cdot (t)) + (10)) \cdot ((2)^{(q) + (2)})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.horizontal_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The rectangle has t+4 rows and q+3 columns. Summing the boundary and interior defect counts yields this identity in natural arithmetic.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.horizontal_sum`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.horizontal_three_rows`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.horizontal_two_columns`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.horizontal_two_rows`
