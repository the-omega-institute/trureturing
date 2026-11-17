# Two-defect king transfers

## Abstract

The finite data support the literal width-five king-grid recurrence.

The source-class certificates supply new domain transition facts. The canonical reconstruction and permutation transport use those facts to obtain the transfer identity for every labelled source.

**Theorem 1.1 (Exact transfer for every labelled boundary).**

$$\forall (p: \operatorname{Data}.\operatorname{Row}), (\forall (d: \operatorname{Nat}), ((\operatorname{Data}.\operatorname{Valid}\left(p, d\right)) \Rightarrow (\forall (s: \operatorname{Fin}\left(43\right)), (\sum_{(r: \operatorname{Data}.\operatorname{Row})} ((\operatorname{if} ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{horizontal}, r, r\right)) \le d) \land (\operatorname{Data}.\operatorname{cl}\left(r, (d) - ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{horizontal}, r, r\right)))\right) = s) \operatorname{then} 1 \operatorname{else} 0)) = \operatorname{Data}.\operatorname{T}\left(\operatorname{Data}.\operatorname{cl}\left(p, d\right), s\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Certificate.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229752: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229752>.

*Commentary.*

For every row p, every valid residual budget d and every output class s, the transfer entry is the sum over labelled next rows r with between(p,r)+horizontal(r,r) <= d and residual class s. Canonical existence and colour-permutation reindexing transport the source-class list certificates to arbitrary p.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Certificate.transition_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/TableBridge](../TableBridge.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes0](Classes0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes1](Classes1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes10](Classes10.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes11](Classes11.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes12](Classes12.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes13](Classes13.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes14](Classes14.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes15](Classes15.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes16](Classes16.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes17](Classes17.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes18](Classes18.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes19](Classes19.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes2](Classes2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes20](Classes20.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes21](Classes21.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes22](Classes22.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes23](Classes23.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes24](Classes24.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes25](Classes25.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes26](Classes26.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes27](Classes27.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes28](Classes28.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes29](Classes29.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes3](Classes3.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes30](Classes30.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes31](Classes31.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes32](Classes32.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes33](Classes33.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes34](Classes34.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes35](Classes35.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes36](Classes36.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes37](Classes37.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes38](Classes38.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes39](Classes39.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes4](Classes4.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes40](Classes40.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes41](Classes41.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes42](Classes42.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes5](Classes5.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes6](Classes6.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes7](Classes7.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes8](Classes8.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes9](Classes9.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Data](Data.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature](ZeroTemperature.md)
