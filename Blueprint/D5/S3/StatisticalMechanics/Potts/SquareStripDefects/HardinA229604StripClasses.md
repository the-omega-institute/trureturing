# Six-column square-lattice strip

## Abstract

Square-lattice strip transfer.

**Theorem 1.1 (transition counts).**

$$\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall s: \operatorname{\mathit{Fin}}\left(96\right), (\sum_{r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right)} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = s)) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)): \operatorname{\mathit{Int}})) = \operatorname{\mathit{HardinA229604StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), s\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripClasses.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

The old active block is supplied by its structural cut identity. Colour permutations preserve all equality tests and bond defects, transporting the canonical source-row identities to every labelled source row.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripClasses.transition_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripClasses](../CrossedStripDefectsWide/WidthSix/HardinA229532StripClasses.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripClasses](HardinA229457StripClasses.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData](HardinA229457StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripCut](HardinA229604StripCut.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData](HardinA229604StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer](ProperTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass0](TwoDefects/First/HardinA229604StripClass0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass1](TwoDefects/First/HardinA229604StripClass1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass10](TwoDefects/First/HardinA229604StripClass10.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass11](TwoDefects/First/HardinA229604StripClass11.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass12](TwoDefects/First/HardinA229604StripClass12.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass13](TwoDefects/First/HardinA229604StripClass13.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass2](TwoDefects/First/HardinA229604StripClass2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass3](TwoDefects/First/HardinA229604StripClass3.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass4](TwoDefects/First/HardinA229604StripClass4.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass5](TwoDefects/First/HardinA229604StripClass5.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass6](TwoDefects/First/HardinA229604StripClass6.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass7](TwoDefects/First/HardinA229604StripClass7.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass8](TwoDefects/First/HardinA229604StripClass8.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass9](TwoDefects/First/HardinA229604StripClass9.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Last/HardinA229604StripClass14](TwoDefects/Last/HardinA229604StripClass14.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Last/HardinA229604StripClass15](TwoDefects/Last/HardinA229604StripClass15.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Last/HardinA229604StripClass16](TwoDefects/Last/HardinA229604StripClass16.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Last/HardinA229604StripClass17](TwoDefects/Last/HardinA229604StripClass17.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Last/HardinA229604StripClass18](TwoDefects/Last/HardinA229604StripClass18.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Last/HardinA229604StripClass19](TwoDefects/Last/HardinA229604StripClass19.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Last/HardinA229604StripClass20](TwoDefects/Last/HardinA229604StripClass20.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Last/HardinA229604StripClass21](TwoDefects/Last/HardinA229604StripClass21.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Last/HardinA229604StripClass22](TwoDefects/Last/HardinA229604StripClass22.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Last/HardinA229604StripClass23](TwoDefects/Last/HardinA229604StripClass23.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Last/HardinA229604StripClass24](TwoDefects/Last/HardinA229604StripClass24.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Last/HardinA229604StripClass25](TwoDefects/Last/HardinA229604StripClass25.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Last/HardinA229604StripClass26](TwoDefects/Last/HardinA229604StripClass26.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData](../StripDefects/HardinA229584StripData.md)
