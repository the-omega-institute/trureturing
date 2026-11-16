# Two-defect king transfers

## Abstract

The finite data support the literal width-six king-grid recurrence.

**Remark 1.1 (Row).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.Row`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Fin 6 -> Fin 4. Rows carry the four labelled colours on six ordered columns.

**Remark 1.2 (horizontal).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.horizontal`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Finset (Fin 6 x Fin 6). The five ordered bonds join consecutive columns.

**Remark 1.3 (between).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.between`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.between` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Finset (Fin 6 x Fin 6). The sixteen ordered bonds comprise six vertical, five diagonal and five antidiagonal bonds.

**Remark 1.4 (Valid).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.Valid`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Row -> Nat -> Prop. A residual budget d is valid when d <= 2 and the current row has at most 2-d horizontal defects.

**Remark 1.5 (cl).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.cl`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Row -> Nat -> Fin 96. The classifier depends only on the row equality pattern and d mod 3, and has 96 values. The class certificates pin every valid canonical source row; colour relabelling extends the result to all rows.

**Remark 1.6 (T).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.T`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Matrix (Fin 96) (Fin 96) Int. This is a 96 by 96 integer matrix. Certificate.transition_counts pins every entry as the exact sum over labelled next rows.

**Remark 1.7 (initial).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.initial`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Fin 96 -> Int. Forward.structural_certificate pins its entries by summing first rows with at most two horizontal defects.

**Remark 1.8 (terminal).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.terminal`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Fin 96 -> Int. Forward.structural_certificate pins the terminal value as the indicator that the residual budget is zero.

**Remark 1.9 (W).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.W`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Fin 12 -> Fin 96 -> Int. The table has twelve rows and 96 columns. Forward.structural_certificate pins W(0), eleven forward steps and the six-term relation at W(11).

**Remark 1.10 (classList).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.classList`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.classList` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Fin 96 -> List (Fin 96). Certificate.class_counts pins the multiplicity of each class as the corresponding matrix entry. These finite lists describe all successor multiplicities without transcribing the matrix.

**Remark 1.11 (successors).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.successors`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.successors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Row -> Nat -> List (Fin 96). Enumerate every labelled next row, retain exactly those within budget, map to its residual-budget class and sort; TableBridge.count_successors identifies each multiplicity with the transfer sum.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.Row`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.between`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.classList`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.horizontal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.successors`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.terminal`
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../../StripDefects/DefectTransfer.md)
