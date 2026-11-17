# Width-six transfer identities

## Abstract

Coordinate identities for width-six king transfers.

This is a domain enumeration of admissible initial rows by class and exact defect budget. Its sum counts labelled rows, and supplies the initial part of the structural transfer certificate.

**Theorem 1.1 (Initial1).**

$$\forall (s: \operatorname{Fin}\left(12\right)), (\sum_{(r: \operatorname{Data}.\operatorname{Row})} ((\operatorname{if} (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{horizontal}, r, r\right) \le 2) \land (\operatorname{Data}.\operatorname{cl}\left(r, (2) - (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{horizontal}, r, r\right))\right) = \operatorname{Fin}.\operatorname{mk}\left((12) + (\operatorname{Fin}.\operatorname{val}\left(s\right))\right)) \operatorname{then} 1 \operatorname{else} 0)) = \operatorname{Data}.\operatorname{initial}\left(\operatorname{Fin}.\operatorname{mk}\left((12) + (\operatorname{Fin}.\operatorname{val}\left(s\right))\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Pins/Initial1.certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

Twelve coordinates of the initial class weights equal the exact labelled first-row sums with at most two horizontal defects.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Pins/Initial1.certificate`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data](../Data.md)
