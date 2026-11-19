# Two-defect king transfers

## Abstract

The finite data support the literal width-six king-grid recurrence.

**Definition 1.1 (Decidability of valid residual budgets).**

$$\forall (p: (\operatorname{Fin}\left(6\right)) \to (\operatorname{Fin}\left(4\right))), (\forall (d: \operatorname{Nat}), (\operatorname{Decidable}\left(\operatorname{Valid}\left(p, d\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.instDecidableValid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The exported instance supplies decidability to the class certificates.

**Definition 1.2 (Row).**

$$\operatorname{Row} = \left((\operatorname{Fin}\left(6\right)) \to (\operatorname{Fin}\left(4\right))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Fin 6 -> Fin 4. Rows carry the four labelled colours on six ordered columns.

**Definition 1.3 (horizontal).**

$$\operatorname{horizontal} = \operatorname{StripDefects}.\operatorname{HardinA229584StripData}.\operatorname{horizontal}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Finset (Fin 6 x Fin 6). The five ordered bonds join consecutive columns. It is defined as StripDefects.HardinA229584StripData.horizontal.

**Definition 1.4 (between).**

$$\operatorname{between} = \{(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (1, 0), (2, 1), (3, 2), (4, 3), (5, 4)\}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.between` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Finset (Fin 6 x Fin 6). The sixteen ordered bonds comprise six vertical, five diagonal and five antidiagonal bonds.

**Definition 1.5 (Valid).**

$$\forall (p: (\operatorname{Fin}\left(6\right)) \to (\operatorname{Fin}\left(4\right))), (\forall (d: \operatorname{Nat}), ((\operatorname{Valid}\left(p, d\right)) \Leftrightarrow ((d \le 2) \land (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{horizontal}, p, p\right) \le (2) - (d)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Row -> Nat -> Prop. A residual budget d is valid when d <= 2 and the current row has at most 2-d horizontal defects.

**Remark 1.6 (cl).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.cl`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Row -> Nat -> Fin 96. The classifier depends only on the row equality pattern and d mod 3, and has 96 values. The class certificates pin every valid canonical source row; colour relabelling extends the result to all rows.

**Definition 1.7 (Proper zero-budget successors).**

$$\forall (p: (\operatorname{Fin}\left(6\right)) \to (\operatorname{Fin}\left(4\right))), (\operatorname{properSuccessors}\left(p\right) = \operatorname{List}.\operatorname{insertionSort}\left((\lambda (a: \operatorname{Fin}\left(96\right)) \mapsto (\lambda (b: \operatorname{Fin}\left(96\right)) \mapsto a \le b)), \operatorname{List}.\operatorname{map}\left((\lambda (v: \operatorname{Fin}\left(4\right)) \mapsto \operatorname{cl}\left((\lambda (j: \operatorname{Fin}\left(6\right)) \mapsto \operatorname{Fin}.\operatorname{xor}\left(v, p\left(j\right)\right)), 0\right)), \operatorname{List}.\operatorname{filter}\left((\lambda (v: \operatorname{Fin}\left(4\right)) \mapsto v \in \operatorname{HardinA233166KingStrip}.\operatorname{offsetChoices}\left((\lambda (j: \operatorname{Fin}\left(6\right)) \mapsto \operatorname{Fin}.\operatorname{xor}\left(p\left(0\right), p\left(j\right)\right))\right)), \operatorname{List}.\operatorname{finRange}\left(4\right)\right)\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.properSuccessors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Row -> List (Fin 96). Map the original width-six owner's allowed xor shifts through the existing class map and sort. Each allowed shift contributes exactly one labelled successor.

**Remark 1.8 (T).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.T`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Matrix (Fin 96) (Fin 96) Int. This is a 96 by 96 integer matrix. Proper zero-budget rows count properSuccessors at representative rows; all other rows retain their exact defect data. Certificate.transition_counts pins every entry as the exact sum over labelled next rows.

**Remark 1.9 (initial).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.initial`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Fin 96 -> Int. Forward.structural_certificate pins its entries by summing first rows with at most two horizontal defects.

**Remark 1.10 (terminal).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.terminal`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Fin 96 -> Int. Forward.structural_certificate pins the terminal value as the indicator that the residual budget is zero.

**Remark 1.11 (W).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.W`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Fin 12 -> Fin 96 -> Int. The table has twelve rows and 96 columns. Forward.structural_certificate pins W(0), eleven forward steps and the six-term relation at W(11).

**Remark 1.12 (classList).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.classList`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.classList` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Fin 96 -> List (Fin 96). Counts.Check7.counts pins the multiplicity of each class as the corresponding matrix entry. These finite lists describe all successor multiplicities without transcribing the matrix.

**Definition 1.13 (successors).**

$$\forall (p: (\operatorname{Fin}\left(6\right)) \to (\operatorname{Fin}\left(4\right))), (\forall (d: \operatorname{Nat}), (\operatorname{successors}\left(p, d\right) = (\operatorname{if} ((d = 0) \land (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{horizontal}, p, p\right) = 0)) \operatorname{then} \operatorname{properSuccessors}\left(p\right) \operatorname{else} \operatorname{List}.\operatorname{insertionSort}\left((\lambda (a: \operatorname{Fin}\left(96\right)) \mapsto (\lambda (b: \operatorname{Fin}\left(96\right)) \mapsto a \le b)), \operatorname{List}.\operatorname{filterMap}\left((\lambda (r: (\operatorname{Fin}\left(6\right)) \to (\operatorname{Fin}\left(4\right))) \mapsto (\operatorname{if} ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{horizontal}, r, r\right)) \le d) \operatorname{then} \operatorname{some}\left(\operatorname{cl}\left(r, (d) - ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{horizontal}, r, r\right)))\right)\right) \operatorname{else} \operatorname{none})), \operatorname{List}.\operatorname{ofFn}\left((\lambda (i: \operatorname{Fin}\left((4)^{6}\right)) \mapsto \operatorname{Equiv}.\operatorname{symm}\left(\operatorname{finFunctionFinEquiv}, i\right))\right)\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.successors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The Lean type is Row -> Nat -> List (Fin 96). For a horizontally proper source at zero budget use properSuccessors. Otherwise enumerate every labelled next row, retain those within budget, map to its residual-budget class and sort; TableBridge.count_successors identifies each multiplicity with the transfer sum.

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
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.instDecidableValid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.properSuccessors`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.successors`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip](../../../../../Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData](../../../StripDefects/HardinA229584StripData.md)
