# Two-defect king transfers

## Abstract

The finite data support the literal width-4 king-grid recurrence.

**Remark 1.1 (horizontal).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.horizontal`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is Finset (Fin 4 x Fin 4). The 3 ordered bonds join consecutive columns. This consumed alias delegates to StripDefects.HardinA229582Strip.horizontal. It is bind-only.

**Remark 1.2 (between).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.between`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.between` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is Finset (Fin 4 x Fin 4). The 10 ordered bonds comprise 4 vertical, 3 diagonal and 3 antidiagonal bonds.

**Remark 1.3 (Valid).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.Valid`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is HardinA233164KingStrip.Boundary -> Nat -> Prop. A residual budget d is valid when d <= 2 and the current row has at most 2-d horizontal defects.

**Remark 1.4 (cl).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.cl`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is HardinA233164KingStrip.Boundary -> Nat -> Fin 19. The classifier depends only on the row equality pattern and d mod 3, and has 19 values. The class certificates pin every valid canonical source row; colour relabelling extends the result to all rows.

**Remark 1.5 (T).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.T`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is Matrix (Fin 19) (Fin 19) Int. This is a 19 by 19 integer matrix. Certificate.transition_counts pins every entry as the exact sum over labelled next rows.

**Remark 1.6 (initial).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.initial`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is Fin 19 -> Int. Forward.structural_certificate pins its entries by summing first rows with at most two horizontal defects.

**Remark 1.7 (terminal).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.terminal`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is Fin 19 -> Int. Forward.structural_certificate pins the terminal value as the indicator that the residual budget is zero.

**Remark 1.8 (W).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.W`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is Fin 12 -> Fin 19 -> Int. The table has twelve rows and 19 columns. Forward.structural_certificate pins W(0), eleven forward steps and the six-term relation at W(11).

**Remark 1.9 (classList).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.classList`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.classList` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is Fin 19 -> List (Fin 19). Certificate.class_counts pins the multiplicity of each remaining class as the corresponding matrix entry. The two productive proper zero-budget classes use empty list placeholders; ZeroTemperature.transition_counts supplies their transfer entries directly from the saturated signed owner. These finite lists describe all successor multiplicities without transcribing the matrix.

**Remark 1.10 (successors).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.successors`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.successors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is HardinA233164KingStrip.Boundary -> Nat -> List (Fin 19). Enumerate every labelled next row, retain exactly those within budget, map to its residual-budget class and sort; TableBridge.count_successors identifies each multiplicity with the transfer sum.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.between`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.classList`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.horizontal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.successors`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233164KingStrip](../../../../../Combinatorics/TraceAvoidingArrays/HardinA233164KingStrip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip](../../../StripDefects/HardinA229582Strip.md)
