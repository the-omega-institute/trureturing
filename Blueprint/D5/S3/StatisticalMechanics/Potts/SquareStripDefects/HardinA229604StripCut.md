# Six-column square-lattice strip

## Abstract

Square-lattice strip transfer.

**Theorem 1.1 (active cut).**

$$\forall r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall c: \operatorname{\mathit{Nat}}, (\forall d: \operatorname{\mathit{Fin}}\left(3\right), (\forall j: \operatorname{\mathit{Fin}}\left(42\right), ((0 < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \implies (((c \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - c\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(54, j\right))) \iff ((c \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - 1) \land (\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - 1 - c\right) = j)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripCut.active_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

A transition into an old active class leaves positive residual budget. Subtracting one from both budgets gives exactly the old class condition.

**Theorem 1.2 (leading counts).**

$$\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall j: \operatorname{\mathit{Fin}}\left(42\right), (\sum_{r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right)} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(54, j\right))) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)): \operatorname{\mathit{Int}})) = \operatorname{\mathit{HardinA229604StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(54, j\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripCut.leading_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

The leading 42 target classes use the old transition counts. Zero residual budget cannot enter any of those classes.

**Theorem 1.3 (terminal counts).**

$$\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) \le 1) \implies (\forall j: \operatorname{\mathit{Fin}}\left(32\right), (\sum_{r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right)} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 0) \land (\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{cl}}\left(r, 0 - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(22, \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(42, j\right)\right))) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)): \operatorname{\mathit{Int}})) = \operatorname{\mathit{HardinA229604StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{cl}}\left(p, 0\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(22, \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(42, j\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripCut.terminal_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

The copied terminal block counts zero-cost successors of rows with at most one horizontal defect, using the old terminal-sector identity.

**Theorem 1.4 (One-defect counts).**

$$\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \implies (\forall j: \operatorname{\mathit{Fin}}\left(32\right), (\sum_{r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right)} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 1) \land (\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{cl}}\left(r, 1 - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(22, \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(42, j\right)\right))) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)): \operatorname{\mathit{Int}})) = \operatorname{\mathit{HardinA229604StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{cl}}\left(p, 1\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(22, \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(42, j\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripCut.one_defect_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

For a source row with no horizontal defect and residual budget one, successors contributing to the sum have cost zero or one. Cost zero leaves a class below 42, whereas cost one shifts the old terminal class by 32. Larger costs contribute zero. The 10 by 32 crossing block is exactly the corresponding one-defect matrix block, so HardinA229457StripClasses.transition_counts at budget one supplies the sum without any canonical-row hypothesis.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripCut.active_cut`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripCut.leading_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripCut.one_defect_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripCut.terminal_counts`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripData](../CrossedStripDefectsWide/WidthSix/HardinA229532StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripClasses](HardinA229457StripClasses.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData](HardinA229457StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData](HardinA229604StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer](ProperTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData](../StripDefects/HardinA229584StripData.md)
