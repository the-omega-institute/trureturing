# Two-defect king transfers

## Abstract

The finite data support the literal fixed-width king-grid recurrence.

The defect count of a row list is the sum of its horizontal row costs and consecutive-row interface costs. Under the king-bond formulas, this sum equals the number of monochromatic grid bonds.

**Theorem 1.1 (Row-list costs as two finite sums).**

$$\forall (q: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\forall (H: \operatorname{Finset}\left((\operatorname{Fin}\left(k\right)) \times (\operatorname{Fin}\left(k\right))\right)), (\forall (V: \operatorname{Finset}\left((\operatorname{Fin}\left(k\right)) \times (\operatorname{Fin}\left(k\right))\right)), (\forall (n: \operatorname{Nat}), (\forall (f: (\operatorname{Fin}\left((n) + (1)\right)) \to (\operatorname{DefectTransfer}.\operatorname{Row}\left(q, k\right))), (\operatorname{DefectTransfer}.\operatorname{defects}\left(H, V, \operatorname{List}.\operatorname{ofFn}\left(f\right)\right) = (\sum_{(i: \operatorname{Fin}\left((n) + (1)\right))} (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(H, \operatorname{f}\left(i\right), \operatorname{f}\left(i\right)\right))) + (\sum_{(i: \operatorname{Fin}\left(n\right))} (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(V, \operatorname{f}\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right), \operatorname{f}\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/GridBridge.defects_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

For arbitrary palette, width, bond sets H and V and n+1 rows, the list cost equals the sum of all n+1 horizontal row costs plus the sum of the n costs between consecutive rows. Induction on n includes the single-row boundary.

**Theorem 1.2 (The row-list count is the literal labelled grid count).**

$$\forall (k: \operatorname{Nat}), (\forall (H: \operatorname{Finset}\left((\operatorname{Fin}\left(k\right)) \times (\operatorname{Fin}\left(k\right))\right)), (\forall (V: \operatorname{Finset}\left((\operatorname{Fin}\left(k\right)) \times (\operatorname{Fin}\left(k\right))\right)), ((\forall (r: \operatorname{DefectTransfer}.\operatorname{Row}\left(4, k\right)), (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(H, r, r\right) = \sum_{(j: \operatorname{Fin}\left((k) - (1)\right))} ((\operatorname{if} \operatorname{r}\left(\operatorname{KingGrid}.\operatorname{lo}\left(j\right)\right) = \operatorname{r}\left(\operatorname{KingGrid}.\operatorname{hi}\left(j\right)\right) \operatorname{then} 1 \operatorname{else} 0)))) \Rightarrow ((\forall (r: \operatorname{DefectTransfer}.\operatorname{Row}\left(4, k\right)), (\forall (t: \operatorname{DefectTransfer}.\operatorname{Row}\left(4, k\right)), (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(V, r, t\right) = ((\sum_{(j: \operatorname{Fin}\left(k\right))} ((\operatorname{if} \operatorname{r}\left(j\right) = \operatorname{t}\left(j\right) \operatorname{then} 1 \operatorname{else} 0))) + (\sum_{(j: \operatorname{Fin}\left((k) - (1)\right))} ((\operatorname{if} \operatorname{r}\left(\operatorname{KingGrid}.\operatorname{lo}\left(j\right)\right) = \operatorname{t}\left(\operatorname{KingGrid}.\operatorname{hi}\left(j\right)\right) \operatorname{then} 1 \operatorname{else} 0)))) + (\sum_{(j: \operatorname{Fin}\left((k) - (1)\right))} ((\operatorname{if} \operatorname{r}\left(\operatorname{KingGrid}.\operatorname{hi}\left(j\right)\right) = \operatorname{t}\left(\operatorname{KingGrid}.\operatorname{lo}\left(j\right)\right) \operatorname{then} 1 \operatorname{else} 0)))))) \Rightarrow (\forall (n: \operatorname{Nat}), (\operatorname{DefectTransfer}.\operatorname{literalCount}\left(H, V, 2, (n) + (1)\right) = \operatorname{KingTwoGrid}.\operatorname{L}\left((n) + (1), k\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/GridBridge.literal_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

Assume H counts adjacent horizontal bonds and V counts the vertical, diagonal and antidiagonal bonds. At every height n+1, the exact two-defect literalCount equals KingTwoGrid.L. KingGrid.sum_edges identifies the four disjoint edge families; the underlying colourings and cell order are identical.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/GridBridge.defects_rows`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/GridBridge.literal_bridge`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid](../KingGrid.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid](../KingTwoGrid.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
