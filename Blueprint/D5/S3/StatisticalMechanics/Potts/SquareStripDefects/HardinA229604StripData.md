# Six-column square-lattice strip

## Abstract

Square-lattice strip transfer.

**Definition 1.1 (Valid).**

$$\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Nat}}, ((\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right)) \iff ((d \le 2) \land (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) \le 2 - d))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

The residual budget is bounded by two, and the horizontal defects of the current row use at most the complementary budget.

**Definition 1.2 (Residual state decision).**

$$\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Nat}}, ((\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{decidableValid}}\left(p, d\right): \operatorname{\mathit{Decidable}}\left(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right)\right)) = \operatorname{\mathit{inferInstanceAs}}\left(\operatorname{\mathit{Decidable}}\left((d \le 2) \land (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) \le 2 - d)\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.decidableValid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

The right-hand side is inferInstanceAs applied to Decidable of the displayed conjunction. It combines the decisions for the two natural-number inequalities defining Valid.

**Definition 1.3 (cl).**

$$\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = (\operatorname{\mathit{if}} (0 < d) \operatorname{\mathit{then}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(54, \operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{cl}}\left(p, d - 1\right)\right)) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) \le 1) \operatorname{\mathit{then}} ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{cl}}\left(p, 0\right)\right) + 32\right): \operatorname{\mathit{Fin}}\left(96\right))) \operatorname{\mathit{else}} (((\lambda c: \operatorname{\mathit{Nat}} \mapsto ((\operatorname{\mathit{if}} (c \in \left\{9387, 29122\right\}) \operatorname{\mathit{then}} (74) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{1195, 29120\right\}) \operatorname{\mathit{then}} (75) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{2355, 28700\right\}) \operatorname{\mathit{then}} (76) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{8227, 28674\right\}) \operatorname{\mathit{then}} (77) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{6349, 19876\right\}) \operatorname{\mathit{then}} (78) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{4301, 19872\right\}) \operatorname{\mathit{then}} (79) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{19525\right\}) \operatorname{\mathit{then}} (80) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{16453, 19457\right\}) \operatorname{\mathit{then}} (81) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{10889, 17286\right\}) \operatorname{\mathit{then}} (82) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{649, 17280\right\}) \operatorname{\mathit{then}} (83) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{785, 16920\right\}) \operatorname{\mathit{then}} (84) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{10753, 16902\right\}) \operatorname{\mathit{then}} (85) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{16793\right\}) \operatorname{\mathit{then}} (86) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{4369, 16440\right\}) \operatorname{\mathit{then}} (87) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{6145, 16420\right\}) \operatorname{\mathit{then}} (88) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{5902, 11112\right\}) \operatorname{\mathit{then}} (89) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{5646, 11104\right\}) \operatorname{\mathit{then}} (90) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{6444\right\}) \operatorname{\mathit{then}} (91) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{4140, 6432\right\}) \operatorname{\mathit{then}} (92) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{616, 5888\right\}) \operatorname{\mathit{then}} (93) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{624, 5648\right\}) \operatorname{\mathit{then}} (94) \operatorname{\mathit{else}} (95))))))))))))))))))))))))))))))))))))))))))))\left(\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{equalityPatternCode}}\left(p\right)\right): \operatorname{\mathit{Fin}}\left(96\right))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

Positive residual budgets use the one-defect class after subtracting one. At residual zero with at most one horizontal defect, add 32 to the one-defect class. At residual zero with more than one horizontal defect, use HardinA229532StripData.equalityPatternCode from CrossedStripDefectsWide.WidthSix, with a bit for each column pair in lexicographic order. Natural subtraction truncates at zero. Fin.castAdd preserves the index value in a larger finite type.

**Definition 1.4 (T).**

$$(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{T}: \operatorname{\mathit{Fin}}\left(96\right) \to \left(\operatorname{\mathit{Fin}}\left(96\right) \to \operatorname{\mathit{Int}}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

For i, j of type Fin 96, guards and offsets use Fin.val i and Fin.val j. All entries are integers. If both values are below 42, apply HardinA229457StripData.T to the Fin 42 indices formed from Fin.val i and Fin.val j using those bounds. If i is at least 42 and j is below 42, the entry is 0.

The 32 by 54 crossing table has a 10 by 54 upper block. For i below 10 and j at least 42, use row i and column j − 42 of that block. The bottom 22 rows consist of a 22 by 32 integer block followed by 22 zero columns. For i from 20 through 41 and j from 42 through 73, use row i − 20 and column j − 42 of the 22 by 32 block. For the same source rows and j from 74 through 95, the entry is 0.

For i from 10 through 19 and j from 42 through 73, apply HardinA229457StripData.T to the Fin 42 indices with values Fin.val i − 10 and Fin.val j − 32. For i and j both from 42 through 73, apply it to the Fin 42 indices with values Fin.val i − 32 and Fin.val j − 32. The branch bounds justify each reconstruction.

For i at least 74 and j from 42 through 51, the entry is at row i − 74 and column j − 42 of the new 22 by 10 integer table. Every other entry is 0. Among Valid states, indices 74 through 95 represent rows with two horizontal defects. The total classifier also sends a constant row at residual zero to class 95, outside Valid because its horizontal cost is five.

HardinA229604StripClasses.transition_counts identifies the entries with the successor sums. The literal entries are given by [crossing and lastRows](../../../../../../D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.lean#L71-L129).

Finite partition refinement of the 96 states, starting with terminal acceptance and splitting by successor counts into each block, stabilizes at 94 classes.

**Definition 1.5 (initial).**

$$(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{initial}}: \operatorname{\mathit{Fin}}\left(96\right) \to \operatorname{\mathit{Int}})$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

For j of type Fin 96, use Fin.val j in the guards and offsets. If Fin.val j is below 42, apply HardinA229457StripData.initial to the Fin 42 index formed from Fin.val j using that bound. If Fin.val j is from 42 through 73, the entry is 0.

For j from 74 through 95, the entry at local index j − 74 is taken from the new integer row (12, 12, 12, 12, 12, 12, 6, 12, 12, 12, 12, 12, 6, 12, 12, 12, 12, 6, 12, 12, 12, 6). HardinA229604Strip.finite_certificate identifies the resulting entries with the literal first-row counts.

**Definition 1.6 (terminal).**

$$(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{terminal}}: \operatorname{\mathit{Fin}}\left(96\right) \to \operatorname{\mathit{Int}})$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

Fin.append joins 42 zeros, the coordinates HardinA229457StripData.terminal (Fin.natAdd 10 j) for j of type Fin 32, and 22 ones for classes 74 through 95, which represent rows with two horizontal defects among Valid states. For a Valid state, it accepts exactly residual budget zero.

**Definition 1.7 (W).**

$$(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{W}: \operatorname{\mathit{Fin}}\left(25\right) \to \left(\operatorname{\mathit{Fin}}\left(96\right) \to \operatorname{\mathit{Int}}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

For k : Fin 25 and j : Fin 96, use the natural values of the indices in these ranges. For j below 42, W k j equals HardinA229457StripData.W (Fin.castAdd 1 k) j, with j read in Fin 42. The cast embeds k into Fin 26 with the same value.

For j at least 42 and k = 0, W k j is initial j. For j at least 42 and k at least 1, W k j is at row k − 1 and column j − 42 of the new 24 by 54 integer table.

HardinA229604StripPowers.steps gives the initial row and the product of each preceding row with T. The 24 by 54 table is the literal tail of the Fin.cons argument to [W](../../../../../../D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.lean#L154).

**Theorem 1.8 (leading block).**

$$\forall i: \operatorname{\mathit{Fin}}\left(42\right), (\forall j: \operatorname{\mathit{Fin}}\left(42\right), (\operatorname{\mathit{HardinA229604StripData}}.\operatorname{T}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(54, i\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(54, j\right)\right) = \operatorname{\mathit{HardinA229457StripData}}.\operatorname{T}\left(i, j\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.leading_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

The displayed embeddings identify this whole matrix block with the original one-defect transfer. Fin.natAdd adds its leading natural offset.

**Theorem 1.9 (terminal block).**

$$\forall i: \operatorname{\mathit{Fin}}\left(32\right), (\forall j: \operatorname{\mathit{Fin}}\left(32\right), (\operatorname{\mathit{HardinA229604StripData}}.\operatorname{T}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(22, \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(42, i\right)\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(22, \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(42, j\right)\right)\right) = \operatorname{\mathit{HardinA229457StripData}}.\operatorname{T}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(10, i\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(10, j\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.terminal_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

The displayed embeddings identify this whole matrix block with the original one-defect transfer. Fin.natAdd adds its leading natural offset.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.decidableValid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.leading_block`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.terminal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.terminal_block`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripData](../CrossedStripDefectsWide/WidthSix/HardinA229532StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData](HardinA229457StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData](../StripDefects/HardinA229584StripData.md)
