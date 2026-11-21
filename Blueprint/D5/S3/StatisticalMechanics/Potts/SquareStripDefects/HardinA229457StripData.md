# Six-column square-lattice strip

## Abstract

Square-lattice strip transfer.

**Definition 1.1 (Valid).**

$$\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Nat}}, ((\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right)) \iff (\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

The imported predicate requires d ≤ 1 and bondDefects horizontal p p ≤ 1 - d, where natural subtraction truncates at zero. The residual budget is bounded by one and the current row can use only its complementary part.

**Definition 1.2 (Residual state decision).**

$$\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Nat}}, ((\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{decidableValid}}\left(p, d\right): \operatorname{\mathit{Decidable}}\left(\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right)\right)) = \operatorname{\mathit{inferInstanceAs}}\left(\operatorname{\mathit{Decidable}}\left(\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right)\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.decidableValid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

The right-hand side is inferInstanceAs applied to Decidable of HardinA229532StripData.Valid p d. The imported predicate supplies its existing decision instance.

**Definition 1.3 (cl).**

$$\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = ((\operatorname{\mathit{if}} (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \operatorname{\mathit{then}} ((\operatorname{\mathit{if}} (0 < d) \operatorname{\mathit{then}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(32, \operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{cl}}\left(p\right)\right)) \operatorname{\mathit{else}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(22, \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(10, \operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{cl}}\left(p\right)\right)\right)))) \operatorname{\mathit{else}} ((\lambda c: \operatorname{\mathit{Nat}} \mapsto ((\operatorname{\mathit{if}} (\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = 26) \operatorname{\mathit{then}} (20) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{1093, 19520\right\}) \operatorname{\mathit{then}} (21) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{if}} (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) = 1) \operatorname{\mathit{then}} (\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{cl}}\left(p, 0\right) = 30) \operatorname{\mathit{else}} (c \in \left\{8533, 19482\right\}))) \operatorname{\mathit{then}} (22) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = 29) \operatorname{\mathit{then}} (23) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{2185, 16772\right\}) \operatorname{\mathit{then}} (24) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{8329, 16770\right\}) \operatorname{\mathit{then}} (25) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{1297, 16472\right\}) \operatorname{\mathit{then}} (26) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = 25) \operatorname{\mathit{then}} (27) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{10902\right\}) \operatorname{\mathit{then}} (28) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{646, 10880\right\}) \operatorname{\mathit{then}} (29) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{10774\right\}) \operatorname{\mathit{then}} (30) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{774, 10760\right\}) \operatorname{\mathit{then}} (31) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{6354, 9396\right\}) \operatorname{\mathit{then}} (32) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{4290, 9376\right\}) \operatorname{\mathit{then}} (33) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{6162, 8244\right\}) \operatorname{\mathit{then}} (34) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = 22) \operatorname{\mathit{then}} (35) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{1188, 6336\right\}) \operatorname{\mathit{then}} (36) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{2340, 6156\right\}) \operatorname{\mathit{then}} (37) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = 21) \operatorname{\mathit{then}} (38) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{1200, 4304\right\}) \operatorname{\mathit{then}} (39) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{776\right\}) \operatorname{\mathit{then}} (40) \operatorname{\mathit{else}} (41))))))))))))))))))))))))))))))))))))))))))))\left(\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{equalityPatternCode}}\left(p\right)\right))): \operatorname{\mathit{Fin}}\left(42\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

The five tests for output classes 20, 23, 27, 35 and 38 call HardinA229532StripData.cl p d with target indices 26, 29, 25, 22 and 21 respectively. The test for class 22 calls HardinA229532StripData.cl p 0 at index 30 when the horizontal defect count is one. Its other case and the remaining signature tests use HardinA229532StripData.equalityPatternCode. Reflection pairs are retained separately whenever the later budget extension distinguishes them. Fin.castAdd preserves an index value in a larger finite type; Fin.natAdd adds its leading natural offset.

**Definition 1.4 (T).**

$$(\operatorname{\mathit{HardinA229457StripData}}.\operatorname{T}: \operatorname{\mathit{Fin}}\left(42\right) \to \left(\operatorname{\mathit{Fin}}\left(42\right) \to \operatorname{\mathit{Int}}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

For i, j : Fin 42, write i and j for their natural values in the index ranges below. All matrix entries are integers. The indices 0 through 9 and 10 through 19 are the proper-row classes with positive and zero residual budget, respectively. Indices 20 through 41 are the rows with one horizontal defect.

If i and j are both below 10, the entry is ProperTransfer.T i j. If i is below 10 and j is at least 10, the entry is at row i and column j − 10 of the new 10 by 32 crossing table.

If i and j are both in 10 through 19, the entry is ProperTransfer.T (i − 10) (j − 10). If i is at least 20 and j is in 10 through 19, the entry is at row i − 20 and column j − 10 of the new 22 by 10 table for rows with one horizontal defect. Every other entry is 0.

HardinA229457StripClasses.transition_counts identifies the entries with the successor sums. The literal entries are given by [crossing and lastRows](../../../../../../D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.lean#L78-L111).

**Definition 1.5 (initial).**

$$(\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{initial}}: \operatorname{\mathit{Fin}}\left(42\right) \to \operatorname{\mathit{Int}})$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

For j : Fin 42, the following cases use the natural value of j. For j below 10, let d(j) = HardinA233127SquareStrip.distribution 0 (j + 1) and d₀ = HardinA233127SquareStrip.distribution 0 0. At j = 0 the entry is (6 · d(j) + 3 · d₀) / 8. At j in 1 through 9 it is 6 · d(j) / 8. Both divisions are in Int. The entries at j in 10 through 19 are 0.

In the final block, the entries at j = 20, 22, 23, 27, 35 and 38 are the entries of HardinA229532StripData.initial at 26, 30, 29, 25, 22 and 21, respectively. The remaining entries are 6 at j = 28, 30, 40 and 41, and 12 at every other index in 20 through 41.

HardinA229457Strip.finite_certificate identifies each entry with its literal first-row count.

**Definition 1.6 (terminal).**

$$\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{terminal}} = \begin{pmatrix}0&0&0&0&0&0&0&0&0&0&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1\end{pmatrix}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

For a row p and residual d satisfying HardinA229457StripData.Valid p d, the terminal entry at HardinA229457StripData.cl p d is 1 exactly when d is zero. The vector has 42 integer coordinates. Fin.append joins ten zeros, the ten proper-coordinate entries of HardinA233127SquareStrip.w 0, and 22 ones for the rows with a horizontal defect.

**Definition 1.7 (W).**

$$(\operatorname{\mathit{HardinA229457StripData}}.\operatorname{W}: \operatorname{\mathit{Fin}}\left(26\right) \to \left(\operatorname{\mathit{Fin}}\left(42\right) \to \operatorname{\mathit{Int}}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

For k of type Fin 26 and j of type Fin 42 with Fin.val j below 10, W k j equals initial j times HardinA233127SquareStrip.w (Fin.val k) applied at the Fin 11 index of value Fin.val j + 1, divided in Int by 64 raised to Fin.val k.

For Fin.val j at least 10 and Fin.val k = 0, W k j is initial j. For Fin.val j at least 10 and Fin.val k at least 1, W k j is at row Fin.val k − 1 and column Fin.val j − 10 of the new 25 by 32 integer table.

HardinA229457StripPowers.steps gives the initial row and the product of each preceding row with T. The 25 by 32 table is the literal tail of the Fin.cons argument to [W](../../../../../../D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.lean#L136).

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.decidableValid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip](../../../Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripData](../CrossedStripDefectsWide/WidthSix/HardinA229532StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer](ProperTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData](../StripDefects/HardinA229584StripData.md)
