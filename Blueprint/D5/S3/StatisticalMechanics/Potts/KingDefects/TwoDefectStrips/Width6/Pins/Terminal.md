# Width-six transfer identities

## Abstract

Coordinate identities for width-six king transfers.

For every admissible six-position row and residual budget, the terminal class value is the indicator that the residual budget is zero.

**Theorem 1.1 (Terminal).**

$$\forall (p: \operatorname{Data}.\operatorname{Row}), (\forall (d: \operatorname{Fin}\left(3\right)), ((\operatorname{Data}.\operatorname{Valid}\left(p, \operatorname{Fin}.\operatorname{val}\left(d\right)\right)) \Rightarrow (\operatorname{Data}.\operatorname{terminal}\left(\operatorname{Data}.\operatorname{cl}\left(p, \operatorname{Fin}.\operatorname{val}\left(d\right)\right)\right) = (\operatorname{if} \operatorname{Fin}.\operatorname{val}\left(d\right) = 0 \operatorname{then} 1 \operatorname{else} 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Pins/Terminal.certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

At every valid source the terminal class value is one exactly when the residual budget is zero.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Pins/Terminal.certificate`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data](../Data.md)
