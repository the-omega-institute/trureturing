# Two-defect king transfers

## Abstract

The finite data support the literal width-4 king-grid recurrence.

**Definition 1.1 (Decidability of valid residual budgets).**

$$\forall (p: (\operatorname{Fin}\left(4\right)) \to (\operatorname{Fin}\left(4\right))), (\forall (d: \operatorname{Nat}), (\operatorname{Decidable}\left(\operatorname{Valid}\left(p, d\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.instDecidableValid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The exported instance supplies decidability to the class certificates.

**Definition 1.2 (horizontal).**

$$\operatorname{horizontal} = \operatorname{StripDefects}.\operatorname{HardinA229582Strip}.\operatorname{horizontal}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is Finset (Fin 4 x Fin 4). The 3 ordered bonds join consecutive columns. This horizontal edge set agrees with StripDefects.HardinA229582Strip.horizontal.

**Definition 1.3 (between).**

$$\operatorname{between} = \{(0, 0), (1, 1), (2, 2), (3, 3), (0, 1), (1, 2), (2, 3), (1, 0), (2, 1), (3, 2)\}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.between` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is Finset (Fin 4 x Fin 4). The edge set is HardinA229537StripData.between, consisting of pairs (i,j) with i <= j+1 and j <= i+1. Its 10 ordered bonds comprise 4 vertical, 3 diagonal and 3 antidiagonal bonds.

**Definition 1.4 (Valid).**

$$\forall (p: (\operatorname{Fin}\left(4\right)) \to (\operatorname{Fin}\left(4\right))), (\forall (d: \operatorname{Nat}), ((\operatorname{Valid}\left(p, d\right)) \Leftrightarrow ((d \le 2) \land (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{horizontal}, p, p\right) \le (2) - (d)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is HardinA233164KingStrip.Boundary -> Nat -> Prop. A residual budget d is valid when d <= 2 and the current row has at most 2-d horizontal defects.

**Remark 1.5 (cl).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.cl`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is HardinA233164KingStrip.Boundary -> Nat -> Fin 19. The classifier depends only on the row equality pattern and d mod 3, and has 19 values. The class certificates pin every valid canonical source row; colour relabelling extends the result to all rows.

**Remark 1.6 (T).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.T`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is Matrix (Fin 19) (Fin 19) Int. This is a 19 by 19 integer matrix. Certificate.transition_counts pins every entry as the exact sum over labelled next rows.

**Remark 1.7 (initial).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.initial`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is Fin 19 -> Int. Forward.structural_certificate pins its entries by summing first rows with at most two horizontal defects.

**Remark 1.8 (terminal).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.terminal`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is Fin 19 -> Int. Forward.structural_certificate pins the terminal value as the indicator that the residual budget is zero.

**Remark 1.9 (W).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.W`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is Fin 12 -> Fin 19 -> Int. The table has twelve rows and 19 columns. Forward.structural_certificate pins W(0), eleven forward steps and the six-term relation at W(11).

**Remark 1.10 (classList).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.classList`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.classList` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The Lean type is Fin 19 -> List (Fin 19). Certificate.class_counts pins the multiplicity of each remaining class as the corresponding matrix entry. The two productive proper zero-budget classes use empty list placeholders; ZeroTemperature.transition_counts supplies their transfer entries directly from the saturated signed owner. These finite lists describe all successor multiplicities without transcribing the matrix.

**Definition 1.11 (successors).**

$$\forall (p: (\operatorname{Fin}\left(4\right)) \to (\operatorname{Fin}\left(4\right))), (\forall (d: \operatorname{Nat}), (\operatorname{successors}\left(p, d\right) = \operatorname{List}.\operatorname{insertionSort}\left((\lambda (a: \operatorname{Fin}\left(19\right)) \mapsto (\lambda (b: \operatorname{Fin}\left(19\right)) \mapsto a \le b)), \operatorname{List}.\operatorname{filterMap}\left((\lambda (r: (\operatorname{Fin}\left(4\right)) \to (\operatorname{Fin}\left(4\right))) \mapsto (\operatorname{if} ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{horizontal}, r, r\right)) \le d) \operatorname{then} \operatorname{some}\left(\operatorname{cl}\left(r, (d) - ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{horizontal}, r, r\right)))\right)\right) \operatorname{else} \operatorname{none})), \operatorname{List}.\operatorname{ofFn}\left((\lambda (i: \operatorname{Fin}\left((4)^{4}\right)) \mapsto \operatorname{Equiv}.\operatorname{symm}\left(\operatorname{finFunctionFinEquiv}, i\right))\right)\right)\right)))$$

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
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.instDecidableValid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.successors`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233164KingStrip](../../../../../Combinatorics/TraceAvoidingArrays/HardinA233164KingStrip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData](../../../CrossedStripDefectsWide/P4a/HardinA229537StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip](../../../StripDefects/HardinA229582Strip.md)
