# Two-defect king transfers

## Abstract

The finite data support the literal width-3 king-grid recurrence.

**Definition 1.1 (Decidability of valid residual budgets).**

$$\forall (p: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(4\right))), (\forall (d: \operatorname{Nat}), (\operatorname{Decidable}\left(\operatorname{Valid}\left(p, d\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.instDecidableValid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229750: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229750>.

*Commentary.*

The exported instance supplies decidability to the class certificates.

**Definition 1.2 (horizontal).**

$$\operatorname{horizontal} = \operatorname{StripDefects}.\operatorname{HardinA229581Strip}.\operatorname{horizontal}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229750: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229750>.

*Commentary.*

The Lean type is Finset (Fin 3 x Fin 3). The 2 ordered bonds join consecutive columns. This horizontal edge set agrees with StripDefects.HardinA229581Strip.horizontal.

**Definition 1.3 (between).**

$$\operatorname{between} = \{(0, 0), (1, 1), (2, 2), (0, 1), (1, 2), (1, 0), (2, 1)\}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.between` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229750: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229750>.

*Commentary.*

The Lean type is Finset (Fin 3 x Fin 3). The 7 ordered bonds comprise 3 vertical, 2 diagonal and 2 antidiagonal bonds. The same seven between-row edges form CrossedStripDefects.HardinA229536Strip.between.

**Definition 1.4 (Valid).**

$$\forall (p: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(4\right))), (\forall (d: \operatorname{Nat}), ((\operatorname{Valid}\left(p, d\right)) \Leftrightarrow ((d \le 2) \land (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{horizontal}, p, p\right) \le (2) - (d)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229750: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229750>.

*Commentary.*

The Lean type is HardinA233163KingStrip.Boundary -> Nat -> Prop. A residual budget d is valid when d <= 2 and the current row has at most 2-d horizontal defects.

**Remark 1.5 (cl).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.cl`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229750: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229750>.

*Commentary.*

The Lean type is HardinA233163KingStrip.Boundary -> Nat -> Fin 9. The classifier depends only on the row equality pattern and d mod 3, and has 9 values. The class certificates pin every valid canonical source row; colour relabelling extends the result to all rows.

**Remark 1.6 (T).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.T`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229750: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229750>.

*Commentary.*

The Lean type is Matrix (Fin 9) (Fin 9) Int. This is a 9 by 9 integer matrix. Certificate.transition_counts pins every entry as the exact sum over labelled next rows.

**Remark 1.7 (initial).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.initial`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229750: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229750>.

*Commentary.*

The Lean type is Fin 9 -> Int. Forward.structural_certificate pins its entries by summing first rows with at most two horizontal defects.

**Remark 1.8 (terminal).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.terminal`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229750: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229750>.

*Commentary.*

The Lean type is Fin 9 -> Int. Forward.structural_certificate pins the terminal value as the indicator that the residual budget is zero. This zero-budget indicator is the terminal vector CrossedStripDefects.HardinA229632Strip.terminal.

**Remark 1.9 (W).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.W`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229750: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229750>.

*Commentary.*

The Lean type is Fin 9 -> Fin 9 -> Int. The table has nine rows and 9 columns. Forward.structural_certificate pins W(0), eight forward steps and the six-term relation at W(8).

**Remark 1.10 (classList).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.classList`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.classList` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229750: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229750>.

*Commentary.*

The Lean type is Fin 9 -> List (Fin 9). Certificate.class_counts pins the multiplicity of each remaining class as the corresponding matrix entry. The two productive proper zero-budget classes use empty list placeholders; ZeroTemperature.transition_counts supplies their transfer entries directly from the saturated signed owner. These finite lists describe all successor multiplicities without transcribing the matrix.

**Definition 1.11 (successors).**

$$\forall (p: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(4\right))), (\forall (d: \operatorname{Nat}), (\operatorname{successors}\left(p, d\right) = \operatorname{List}.\operatorname{insertionSort}\left((\lambda (a: \operatorname{Fin}\left(9\right)) \mapsto (\lambda (b: \operatorname{Fin}\left(9\right)) \mapsto a \le b)), \operatorname{List}.\operatorname{filterMap}\left((\lambda (r: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(4\right))) \mapsto (\operatorname{if} ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{horizontal}, r, r\right)) \le d) \operatorname{then} \operatorname{some}\left(\operatorname{cl}\left(r, (d) - ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{horizontal}, r, r\right)))\right)\right) \operatorname{else} \operatorname{none})), \operatorname{List}.\operatorname{ofFn}\left((\lambda (i: \operatorname{Fin}\left((4)^{3}\right)) \mapsto \operatorname{Equiv}.\operatorname{symm}\left(\operatorname{finFunctionFinEquiv}, i\right))\right)\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.successors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229750: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229750>.

*Commentary.*

The Lean type is HardinA233163KingStrip.Boundary -> Nat -> List (Fin 9). Enumerate every labelled next row, retain exactly those within budget, map to its residual-budget class and sort; TableBridge.count_successors identifies each multiplicity with the transfer sum.

**Theorem 1.12 (The zero-budget transfer).**

$$\forall (p: \operatorname{HardinA233163KingStrip}.\operatorname{Boundary}), ((\operatorname{HardinA233163KingStrip}.\operatorname{proper}\left(p\right)) \Rightarrow (\forall (s: \operatorname{Fin}\left(9\right)), (\sum_{(r: \operatorname{HardinA233163KingStrip}.\operatorname{Boundary})} ((\operatorname{if} (((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{horizontal}, r, r\right)) \le 0) \land (\operatorname{Data}.\operatorname{cl}\left(r, (0) - ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{horizontal}, r, r\right)))\right) = s)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{Data}.\operatorname{T}\left(\operatorname{Data}.\operatorname{cl}\left(p, 0\right), s\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229750: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229750>.

*Commentary.*

The map beta sends complementary signed colours to the same four-colour label. Every raw boundary has exactly 8 signed preimages, with two independent choices per column. SignedFibres.sum_beta gives the weighted identity with factor 2^3. The signed row predicate is equivalent to zero defects after applying the map. The owner saturated_certificate preserves the productive boundary type and gives the signed rate. Class correspondence transports kind to the two zero-budget classes, so dividing the signed rate by 8 gives the displayed entry. At width 3, the two signed rates are 16 and 8, hence the raw rates are two and one. All sums and matrix entries are integers; the subtraction inside Data.cl is natural subtraction.

The initial and terminal certificates establish the domain interpretation of the table. The Krylov identities normalize the resulting integer entries; the combined certificate retains the domain content.

**Theorem 1.13 (Acceptance, initialization and the forward relation).**

$$(\forall (p: \operatorname{HardinA233163KingStrip}.\operatorname{Boundary}), (\forall (d: \operatorname{Fin}\left(3\right)), ((\operatorname{Data}.\operatorname{Valid}\left(p, \operatorname{Fin}.\operatorname{val}\left(d\right)\right)) \Rightarrow (\operatorname{Data}.\operatorname{terminal}\left(\operatorname{Data}.\operatorname{cl}\left(p, \operatorname{Fin}.\operatorname{val}\left(d\right)\right)\right) = (\operatorname{if} (\operatorname{Fin}.\operatorname{val}\left(d\right) = 0) \operatorname{then} 1 \operatorname{else} 0))))) \land ((\forall (s: \operatorname{Fin}\left(9\right)), (\sum_{(r: \operatorname{HardinA233163KingStrip}.\operatorname{Boundary})} ((\operatorname{if} ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{horizontal}, r, r\right) \le 2) \land (\operatorname{Data}.\operatorname{cl}\left(r, (2) - (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{horizontal}, r, r\right))\right) = s)) \operatorname{then} 1 \operatorname{else} 0)) = \operatorname{Data}.\operatorname{initial}\left(s\right))) \land (((\operatorname{Data}.\operatorname{W}\left(0\right) = \operatorname{Data}.\operatorname{initial}) \land (\forall (i: \operatorname{Fin}\left(8\right)), (\operatorname{Data}.\operatorname{W}\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right) = \operatorname{Matrix}.\operatorname{vecMul}\left(\operatorname{Data}.\operatorname{W}\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right), \operatorname{Data}.\operatorname{T}\right)))) \land (\operatorname{Data}.\operatorname{W}\left(8\right) = \sum_{(j: \operatorname{Fin}\left(6\right))} (\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{Matrix}.\operatorname{vecCons}\left(-8, \operatorname{Matrix}.\operatorname{vecCons}\left(36, \operatorname{Matrix}.\operatorname{vecCons}\left(-66, \operatorname{Matrix}.\operatorname{vecCons}\left(63, \operatorname{Matrix}.\operatorname{vecCons}\left(-33, \operatorname{Matrix}.\operatorname{vecCons}\left(9, \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right)\right)\left(j\right), \operatorname{Data}.\operatorname{W}\left(\operatorname{Fin}.\operatorname{mk}\left((2) + (\operatorname{Fin}.\operatorname{val}\left(j\right))\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.structural_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229750: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229750>.

*Commentary.*

For every valid row and budget, the terminal entry is the zero-budget indicator. The initial vector counts first rows. W(0)=initial and W(i+1)=W(i)T for i=0,...,7. Finally W(8)=-8W(2)+36W(3)-66W(4)+63W(5)-33W(6)+9W(7). Every identity is kernel checked.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.between`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.classList`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.horizontal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.instDecidableValid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.structural_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.successors`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.terminal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.transition_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip](../../../../../Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip](../../../../../Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip](../../../../../Combinatorics/TraceAvoidingArrays/HardinA233196Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229536Strip](../../../CrossedStripDefects/HardinA229536Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229632Strip](../../../CrossedStripDefects/HardinA229632Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229581Strip](../../../StripDefects/HardinA229581Strip.md)
