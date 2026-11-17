# Two-defect king transfers

## Abstract

The finite data support the literal width-4 king-grid recurrence.

The source-class certificates supply new domain transition facts. The canonical reconstruction and permutation transport use those facts to obtain the transfer identity for every labelled source.

**Theorem 1.1 (Exact transfer for every labelled boundary).**

$$\forall (p: \operatorname{HardinA233164KingStrip}.\operatorname{Boundary}), (\forall (d: \operatorname{Nat}), ((\operatorname{Data}.\operatorname{Valid}\left(p, d\right)) \Rightarrow (\forall (s: \operatorname{Fin}\left(19\right)), (\sum_{(r: \operatorname{HardinA233164KingStrip}.\operatorname{Boundary})} ((\operatorname{if} ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{horizontal}, r, r\right)) \le d) \land (\operatorname{Data}.\operatorname{cl}\left(r, (d) - ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{horizontal}, r, r\right)))\right) = s) \operatorname{then} 1 \operatorname{else} 0)) = \operatorname{Data}.\operatorname{T}\left(\operatorname{Data}.\operatorname{cl}\left(p, d\right), s\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Certificate.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

For every row p, every valid residual budget d and every output class s, the transfer entry is the sum over labelled next rows r with between(p,r)+horizontal(r,r) <= d and residual class s. For proper zero-budget boundaries, the saturated signed certificate of HardinA233164KingStrip supplies the count and class preservation, divided by the constant fibre 16. The nonproper ABBA rows in class 14 have the same zero-defect successor constraints as alternating ABAB rows, so the same owner certificate also supplies their entry. Canonical existence and colour-permutation reindexing transport the remaining source-class list certificates to arbitrary p.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Certificate.transition_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/TableBridge](../TableBridge.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes0](Classes0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes1](Classes1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes10](Classes10.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes11](Classes11.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes13](Classes13.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes15](Classes15.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes16](Classes16.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes17](Classes17.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes18](Classes18.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes2](Classes2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes3](Classes3.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes4](Classes4.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes5](Classes5.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes6](Classes6.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes7](Classes7.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes8](Classes8.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes9](Classes9.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data](Data.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/ZeroTemperature](ZeroTemperature.md)
