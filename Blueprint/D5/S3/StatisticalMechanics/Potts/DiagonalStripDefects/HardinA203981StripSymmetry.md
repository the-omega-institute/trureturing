# Symmetries of six-column diagonal bonds

## Abstract

Symmetries of six-column diagonal bonds

**Theorem 1.1 (Ten diagonal-bond indicators).**

$$\forall q: \mathit{Nat}, (\forall p: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(q\right)), (\forall r: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(q\right)), (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), p, r\right) = (\operatorname{\mathit{if}} (p\left(0\right) = r\left(1\right)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0) + (\operatorname{\mathit{if}} (p\left(1\right) = r\left(0\right)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0) + (\operatorname{\mathit{if}} (p\left(1\right) = r\left(2\right)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0) + (\operatorname{\mathit{if}} (p\left(2\right) = r\left(1\right)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0) + (\operatorname{\mathit{if}} (p\left(2\right) = r\left(3\right)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0) + (\operatorname{\mathit{if}} (p\left(3\right) = r\left(2\right)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0) + (\operatorname{\mathit{if}} (p\left(3\right) = r\left(4\right)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0) + (\operatorname{\mathit{if}} (p\left(4\right) = r\left(3\right)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0) + (\operatorname{\mathit{if}} (p\left(4\right) = r\left(5\right)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0) + (\operatorname{\mathit{if}} (p\left(5\right) = r\left(4\right)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripSymmetry.cost_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

Each pair of adjacent columns supplies one diagonal bond in each orientation.

**Theorem 1.2 (Transfer counts are constant on a boundary class).**

$$\forall d: \mathit{Nat}, (\forall p: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall j: \operatorname{\mathit{Fin}}\left(15\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), p, r\right) = d) \land (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = j)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \sum_{r: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{representatives}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{boundary}}\left(p\right)\right), r\right) = d) \land (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = j)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripSymmetry.lift_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

Independent colour permutations on the two parities preserve cost when interchanged on the next row. Reflection exchanges the two triples and preserves cost. HardinA233258PairTransfer supplies the colour invariance and representative of each triple class. The resulting bijections transport each exact-cost sum to its representative.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripSymmetry.cost_formula`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripSymmetry.lift_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer](../../../Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData](HardinA203981StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn](../StripDefects/HardinA229637RowColumn.md)
