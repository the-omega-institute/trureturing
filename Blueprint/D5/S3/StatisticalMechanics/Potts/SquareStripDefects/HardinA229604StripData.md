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

$$\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = (\operatorname{\mathit{if}} (0 < d) \operatorname{\mathit{then}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(54, \operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{cl}}\left(p, d - 1\right)\right)) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) \le 1) \operatorname{\mathit{then}} ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{cl}}\left(p, 0\right)\right) + 32\right): \operatorname{\mathit{Fin}}\left(96\right))) \operatorname{\mathit{else}} (((\lambda c: \operatorname{\mathit{Nat}} \mapsto ((\operatorname{\mathit{if}} (c \in \left\{9387, 29122\right\}) \operatorname{\mathit{then}} (74) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{1195, 29120\right\}) \operatorname{\mathit{then}} (75) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{2355, 28700\right\}) \operatorname{\mathit{then}} (76) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{8227, 28674\right\}) \operatorname{\mathit{then}} (77) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{6349, 19876\right\}) \operatorname{\mathit{then}} (78) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{4301, 19872\right\}) \operatorname{\mathit{then}} (79) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{19525\right\}) \operatorname{\mathit{then}} (80) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{16453, 19457\right\}) \operatorname{\mathit{then}} (81) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{10889, 17286\right\}) \operatorname{\mathit{then}} (82) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{649, 17280\right\}) \operatorname{\mathit{then}} (83) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{785, 16920\right\}) \operatorname{\mathit{then}} (84) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{10753, 16902\right\}) \operatorname{\mathit{then}} (85) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{16793\right\}) \operatorname{\mathit{then}} (86) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{4369, 16440\right\}) \operatorname{\mathit{then}} (87) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{6145, 16420\right\}) \operatorname{\mathit{then}} (88) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{5902, 11112\right\}) \operatorname{\mathit{then}} (89) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{5646, 11104\right\}) \operatorname{\mathit{then}} (90) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{6444\right\}) \operatorname{\mathit{then}} (91) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{4140, 6432\right\}) \operatorname{\mathit{then}} (92) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{616, 5888\right\}) \operatorname{\mathit{then}} (93) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{624, 5648\right\}) \operatorname{\mathit{then}} (94) \operatorname{\mathit{else}} (95))))))))))))))))))))))))))))))))))))))))))))\left((\operatorname{\mathit{if}} (p\left(0\right) = p\left(1\right)) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(0\right) = p\left(2\right)) \operatorname{\mathit{then}} (2) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(0\right) = p\left(3\right)) \operatorname{\mathit{then}} (4) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} (8) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(0\right) = p\left(5\right)) \operatorname{\mathit{then}} (16) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(1\right) = p\left(2\right)) \operatorname{\mathit{then}} (32) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} (64) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(1\right) = p\left(4\right)) \operatorname{\mathit{then}} (128) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(1\right) = p\left(5\right)) \operatorname{\mathit{then}} (256) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(2\right) = p\left(3\right)) \operatorname{\mathit{then}} (512) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(2\right) = p\left(4\right)) \operatorname{\mathit{then}} (1024) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(2\right) = p\left(5\right)) \operatorname{\mathit{then}} (2048) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(3\right) = p\left(4\right)) \operatorname{\mathit{then}} (4096) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(3\right) = p\left(5\right)) \operatorname{\mathit{then}} (8192) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(4\right) = p\left(5\right)) \operatorname{\mathit{then}} (16384) \operatorname{\mathit{else}} (0))\right): \operatorname{\mathit{Fin}}\left(96\right))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

Positive residual budgets use the one-defect class after subtracting one. At residual zero, the old classes are shifted by 32; the remaining classes use equality-pattern codes. Each equal column pair contributes its displayed power of two in lexicographic pair order. Natural subtraction truncates at zero; Fin.castAdd preserves the index value in a larger finite type.

**Definition 1.4 (T).**

$$(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{T}: \operatorname{\mathit{Fin}}\left(96\right) \to \left(\operatorname{\mathit{Fin}}\left(96\right) \to \operatorname{\mathit{Int}}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

This 96 by 96 integer matrix has the old 42 by 42 matrix as its leading block, zero lower-left block, and the old terminal 32 by 32 block shifted to indices 42 through 73. Rows 10 through 19 and columns 42 through 73 use rows 0 through 9 and columns 10 through 41 of HardinA229457StripData.T; their final 22 entries are zero. The other crossing rows are assembled from a new 10 by 54 table and a new 22 by 32 table followed by 22 zero columns. The 22 rows with two horizontal defects use a new 22 by 10 table. The remaining entries count successors into the 54 new terminal coordinates, exactly as pinned by HardinA229604StripClasses.transition_counts. The retained 96 classes refine the 94-class coarsest lumping.

**Definition 1.5 (initial).**

$$(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{initial}}: \operatorname{\mathit{Fin}}\left(96\right) \to \operatorname{\mathit{Int}})$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

The vector has type Fin 96 → Int and 96 entries. Fin.append joins HardinA229457StripData.initial to a vector of 32 zero entries followed by (12,12,12,12,12,12,6,12,12,12,12,12,6,12,12,12,12,6,12,12,12,6). The old 42 entries are taken directly from the one-defect initial vector. HardinA229604Strip.finite_certificate pins this definition to the literal first-row count and obtains the old entries from HardinA229457Strip.finite_certificate through HardinA229604StripCut.active_cut.

**Definition 1.6 (terminal).**

$$\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{terminal}} = \begin{pmatrix}0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&0&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1\end{pmatrix}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

The terminal vector is zero on the first 42 classes and one on the last 54; it accepts exactly residual budget zero. Fin.append joins 42 zeros, the 32 accepted coordinates of HardinA229457StripData.terminal at indices j.natAdd 10, and 22 ones for rows with two horizontal defects.

**Definition 1.7 (W).**

$$(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{W}: \operatorname{\mathit{Fin}}\left(25\right) \to \left(\operatorname{\mathit{Fin}}\left(96\right) \to \operatorname{\mathit{Int}}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

The 25 by 96 integer array contains successive forward row vectors, pinned by HardinA229604StripPowers.steps. Its first 42 columns are exactly HardinA229457StripData.W at the same row index. On the remaining 54 columns, Fin.cons takes row zero from initial and appends the new 24 by 54 table.

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
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData](HardinA229457StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData](../StripDefects/HardinA229584StripData.md)
