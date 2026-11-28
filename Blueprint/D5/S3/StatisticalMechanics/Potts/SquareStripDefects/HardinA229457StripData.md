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

$$\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = ((\operatorname{\mathit{if}} (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \operatorname{\mathit{then}} ((\operatorname{\mathit{if}} (0 < d) \operatorname{\mathit{then}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(32, \operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{cl}}\left(p\right)\right)) \operatorname{\mathit{else}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(22, \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(10, \operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{cl}}\left(p\right)\right)\right)))) \operatorname{\mathit{else}} ((\lambda c: \operatorname{\mathit{Nat}} \mapsto ((\operatorname{\mathit{if}} (\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = 26) \operatorname{\mathit{then}} (20) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{1093, 19520\right\}) \operatorname{\mathit{then}} (21) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{8533, 19482\right\}) \operatorname{\mathit{then}} (22) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = 29) \operatorname{\mathit{then}} (23) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{2185, 16772\right\}) \operatorname{\mathit{then}} (24) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{8329, 16770\right\}) \operatorname{\mathit{then}} (25) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{1297, 16472\right\}) \operatorname{\mathit{then}} (26) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = 25) \operatorname{\mathit{then}} (27) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{10902\right\}) \operatorname{\mathit{then}} (28) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{646, 10880\right\}) \operatorname{\mathit{then}} (29) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{10774\right\}) \operatorname{\mathit{then}} (30) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{774, 10760\right\}) \operatorname{\mathit{then}} (31) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{6354, 9396\right\}) \operatorname{\mathit{then}} (32) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{4290, 9376\right\}) \operatorname{\mathit{then}} (33) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{6162, 8244\right\}) \operatorname{\mathit{then}} (34) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = 22) \operatorname{\mathit{then}} (35) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{1188, 6336\right\}) \operatorname{\mathit{then}} (36) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{2340, 6156\right\}) \operatorname{\mathit{then}} (37) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = 21) \operatorname{\mathit{then}} (38) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{1200, 4304\right\}) \operatorname{\mathit{then}} (39) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (c \in \left\{776\right\}) \operatorname{\mathit{then}} (40) \operatorname{\mathit{else}} (41))))))))))))))))))))))))))))))))))))))))))))\left((\operatorname{\mathit{if}} (p\left(0\right) = p\left(1\right)) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(0\right) = p\left(2\right)) \operatorname{\mathit{then}} (2) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(0\right) = p\left(3\right)) \operatorname{\mathit{then}} (4) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} (8) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(0\right) = p\left(5\right)) \operatorname{\mathit{then}} (16) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(1\right) = p\left(2\right)) \operatorname{\mathit{then}} (32) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} (64) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(1\right) = p\left(4\right)) \operatorname{\mathit{then}} (128) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(1\right) = p\left(5\right)) \operatorname{\mathit{then}} (256) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(2\right) = p\left(3\right)) \operatorname{\mathit{then}} (512) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(2\right) = p\left(4\right)) \operatorname{\mathit{then}} (1024) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(2\right) = p\left(5\right)) \operatorname{\mathit{then}} (2048) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(3\right) = p\left(4\right)) \operatorname{\mathit{then}} (4096) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(3\right) = p\left(5\right)) \operatorname{\mathit{then}} (8192) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (p\left(4\right) = p\left(5\right)) \operatorname{\mathit{then}} (16384) \operatorname{\mathit{else}} (0))\right))): \operatorname{\mathit{Fin}}\left(42\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

The five tests for output classes 20, 23, 27, 35 and 38 call HardinA229532StripData.cl p d with target indices 26, 29, 25, 22 and 21 respectively. The other tests use the displayed equality-pattern code, which adds powers of two for equal column pairs in lexicographic pair order. Reflection pairs are retained separately whenever the later budget extension distinguishes them. Fin.castAdd preserves an index value in a larger finite type; Fin.natAdd adds its leading natural offset.

**Definition 1.4 (T).**

$$(\operatorname{\mathit{HardinA229457StripData}}.\operatorname{T}: \operatorname{\mathit{Fin}}\left(42\right) \to \left(\operatorname{\mathit{Fin}}\left(42\right) \to \operatorname{\mathit{Int}}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

The 42 by 42 integer matrix has the original ten-class proper matrix in both proper diagonal blocks. The only numerical tables are the 10 by 32 block from proper rows with positive residual budget, and the 22 by 10 block from rows with one horizontal defect. All impossible transitions are defined as zero. All remaining entries are pinned by HardinA229457StripClasses.transition_counts, with the displayed class map and the literal successor sum.

**Definition 1.5 (initial).**

$$(\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{initial}}: \operatorname{\mathit{Fin}}\left(42\right) \to \operatorname{\mathit{Int}})$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

The vector has type Fin 42 → Int and 42 entries. Its first ten entries, indexed by j : Fin 10, are (6 times HardinA233127SquareStrip.distribution 0 ⟨j.val + 1⟩ plus 3 times distribution 0 0 when j.val = 0, and zero otherwise), divided in Int by 8. The next ten entries are zero. For global indices 20, 23, 27, 35 and 38, the last block reads HardinA229532StripData.initial at indices 26, 29, 25, 22 and 21 respectively. The remaining entries in that block are 6 at global indices 28, 30, 40 and 41, and 12 elsewhere. Fin.append joins these vectors. HardinA229457Strip.finite_certificate pins the result to the literal first-row count.

**Definition 1.6 (terminal).**

$$\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{terminal}} = \begin{pmatrix}0&0&0&0&0&0&0&0&0&0&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1\end{pmatrix}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

This one by 42 row vector accepts precisely residual budget zero. Fin.append joins ten zeros, the ten proper-coordinate entries of HardinA233127SquareStrip.w 0, and 22 ones for the rows with a horizontal defect.

**Definition 1.7 (W).**

$$(\operatorname{\mathit{HardinA229457StripData}}.\operatorname{W}: \operatorname{\mathit{Fin}}\left(26\right) \to \left(\operatorname{\mathit{Fin}}\left(42\right) \to \operatorname{\mathit{Int}}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

The 26 by 42 integer matrix contains successive forward row vectors. For k : Fin 26 and j : Fin 10, its zero-defect entry W k (j.castAdd 32) is initial (j.castAdd 32) times HardinA233127SquareStrip.w k.val ⟨j.val + 1⟩, divided in Int by 64 to the power k.val. The weighted transfer identity proves this division exact. For the remaining 32 one-defect coordinates, Fin.cons takes row zero from initial and appends the new 25 by 32 table. The complete matrix is pinned by HardinA229457StripPowers.steps: its first row is initial and each next row is the previous row multiplied by T.

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
