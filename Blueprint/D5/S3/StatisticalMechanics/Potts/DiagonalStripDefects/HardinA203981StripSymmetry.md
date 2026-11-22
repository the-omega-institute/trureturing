# Symmetries of six-column diagonal bonds

## Abstract

Symmetries of six-column diagonal bonds

**Theorem 1.1 (Transfer counts are constant on a boundary class).**

$$\forall d: \mathit{Nat}, (\forall t: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(15\right), \operatorname{\mathit{Fin}}\left(15\right), \mathit{Int}\right), ((\forall i: \operatorname{\mathit{Fin}}\left(15\right), (\forall j: \operatorname{\mathit{Fin}}\left(15\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{representatives}}\left(i\right), r\right) = d) \land (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = j)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = t\left(i, j\right)))) \implies (\forall p: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall j: \operatorname{\mathit{Fin}}\left(15\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), p, r\right) = d) \land (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = j)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = t\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{boundary}}\left(p\right), j\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripSymmetry.lift_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

Independent colour permutations on the two parities preserve cost when interchanged on the next row. Reflection exchanges the two triples and preserves cost. HardinA233258PairTransfer supplies the colour invariance and representative of each triple class. The resulting bijections transport each exact-cost sum to its representative.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripSymmetry.lift_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer](../../../Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData](HardinA203981StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn](../StripDefects/HardinA229637RowColumn.md)
