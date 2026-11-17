# Two-defect king transfers

## Abstract

The finite data support the literal width-six king-grid recurrence.

The source-class certificates supply new domain transition facts. The canonical reconstruction and permutation transport use those facts to obtain the transfer identity for every labelled source.

**Theorem 1.1 (Exact transfer for every labelled boundary).**

$$\forall (p: \operatorname{Data}.\operatorname{Row}), (\forall (d: \operatorname{Nat}), ((\operatorname{Data}.\operatorname{Valid}\left(p, d\right)) \Rightarrow (\forall (s: \operatorname{Fin}\left(96\right)), (\sum_{(r: \operatorname{Data}.\operatorname{Row})} ((\operatorname{if} ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{horizontal}, r, r\right)) \le d) \land (\operatorname{Data}.\operatorname{cl}\left(r, (d) - ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{horizontal}, r, r\right)))\right) = s) \operatorname{then} 1 \operatorname{else} 0)) = \operatorname{Data}.\operatorname{T}\left(\operatorname{Data}.\operatorname{cl}\left(p, d\right), s\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Certificate.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

For every row p, every valid residual budget d and every output class s, the transfer entry is the sum over labelled next rows r with between(p,r)+horizontal(r,r) <= d and residual class s. Canonical existence and colour-permutation reindexing transport the source-class list certificates to arbitrary p.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Certificate.transition_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/TableBridge](../TableBridge.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Chunks1/Source43](Chunks1/Source43.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Counts/Check7](Counts/Check7.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Rows](Rows.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Sources](Sources.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature](ZeroTemperature.md)
