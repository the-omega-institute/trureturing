# Six-column square-lattice strip

## Abstract

Square-lattice strip transfer.

**Theorem 1.1 (transition counts).**

$$\forall j: \operatorname{\mathit{Fin}}\left(2\right), (\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies ((\operatorname{\mathit{HardinA233177Canonical}}.\operatorname{\mathit{Canonical}}\left(p\right)) \implies (\sum_{r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right)} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = (\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(56 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right): \operatorname{\mathit{Fin}}\left(96\right)))) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)): \operatorname{\mathit{Int}})) = \operatorname{\mathit{HardinA229604StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), (\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(56 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right): \operatorname{\mathit{Fin}}\left(96\right))\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass7.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

The exact successor sum for these two new target columns is evaluated on canonical source rows. Residual budget zero with at most one horizontal defect, and residual budget one with no horizontal defect, use the one-defect transition identity. The finite calculation covers only source sectors requiring two defects in total.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass7.transition_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripCut](../../HardinA229604StripCut.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData](../../HardinA229604StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer](../../ProperTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData](../../../StripDefects/HardinA229584StripData.md)
