# Six-column square-lattice strip

## Abstract

Square-lattice strip transfer.

**Definition 1.1 (Crossed proper slot).**

$$(\operatorname{\mathit{HardinA229457StripCut}}.\operatorname{\mathit{crossedProperSlot}}: \operatorname{\mathit{Fin}}\left(20\right) \to \operatorname{\mathit{Fin}}\left(20\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripCut.crossedProperSlot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

In slots 0 through 9, the values are (9, 6, 3, 8, 4, 1, 7, 0, 2, 5), in order. In slots 10 through 19, add 10 to each of these values. Fin.append joins the two blocks, and proper_class_map relates each slot to its crossed classifier value.

**Theorem 1.2 (Proper-class correspondence).**

$$\forall r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(2\right), (\forall s: \operatorname{\mathit{Fin}}\left(20\right), ((\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right) = (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(22, s\right): \operatorname{\mathit{Fin}}\left(42\right))) \iff (\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right) = (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(11, \operatorname{\mathit{HardinA229457StripCut}}.\operatorname{\mathit{crossedProperSlot}}\left(s\right)\right): \operatorname{\mathit{Fin}}\left(31\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripCut.proper_class_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

The two classifiers agree on membership in the corresponding proper-row slots at each of the two residual budgets. Fin.castAdd embeds a finite index preserving its value.

**Theorem 1.3 (class cut).**

$$\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(2\right), (\forall s: \operatorname{\mathit{Fin}}\left(20\right), ((((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 1) \land (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right) < 10)) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 0) \land (10 \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right)))) \implies (((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(22, s\right): \operatorname{\mathit{Fin}}\left(42\right)))) \iff ((\operatorname{\mathit{HardinThinGraphTransport}}.\operatorname{\mathit{proper}}\left(r\right)) \land ((\forall i: \operatorname{\mathit{Fin}}\left(6\right), (p\left(i\right) \ne r\left(i\right))) \land (\operatorname{\mathit{HardinA233127SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), r\right) = (\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(\operatorname{\mathit{Nat}}.\operatorname{\mathit{mod}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right), 10\right) + 1\right): \operatorname{\mathit{Fin}}\left(11\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripCut.class_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

A transition staying in the matching proper sector has zero cost. Since both defect counts are nonnegative, zero cost means that every horizontal and vertical bond has distinct endpoints. Nat.mod is the nonnegative natural remainder after division by ten.

**Theorem 1.4 (proper counts).**

$$\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinThinGraphTransport}}.\operatorname{\mathit{proper}}\left(p\right)) \implies (\forall s: \operatorname{\mathit{Fin}}\left(20\right), ((((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 1) \land (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right) < 10)) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 0) \land (10 \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right)))) \implies (\sum_{r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right)} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(22, s\right): \operatorname{\mathit{Fin}}\left(42\right)))) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)): \operatorname{\mathit{Int}})) = \operatorname{\mathit{HardinA229457StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(22, s\right): \operatorname{\mathit{Fin}}\left(42\right))\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripCut.proper_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

The matching proper-column sum is supplied by the saturated scanner identity. Natural remainder chooses its original class.

**Theorem 1.5 (active counts).**

$$\forall j: \operatorname{\mathit{Fin}}\left(10\right), (\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\sum_{r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right)} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(32, j\right))) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)): \operatorname{\mathit{Int}})) = \operatorname{\mathit{HardinA229457StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(32, j\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripCut.active_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

The leading ten target classes use the original proper-colouring matrix. A zero residual budget cannot enter those classes.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripCut.active_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripCut.class_cut`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripCut.crossedProperSlot`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripCut.proper_class_map`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripCut.proper_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows](../../../Combinatorics/TraceAvoidingArrays/HardinA233127Rows.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip](../../../Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport](../../../Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripCut](../CrossedStripDefectsWide/WidthSix/HardinA229532StripCut.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripData](../CrossedStripDefectsWide/WidthSix/HardinA229532StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData](HardinA229457StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer](ProperTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData](../StripDefects/HardinA229584StripData.md)
