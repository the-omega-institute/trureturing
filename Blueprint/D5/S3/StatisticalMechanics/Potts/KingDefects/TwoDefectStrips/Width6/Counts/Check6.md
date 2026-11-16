# Width-six class counts

## Abstract

Exact multiplicities of successor classes.

**Theorem 1.1 (First 84 classes).**

$$\forall (c: \operatorname{Fin}\left(84\right)), (\forall (s: \operatorname{Fin}\left(96\right)), (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{List}.\operatorname{count}\left(s, \operatorname{Data}.\operatorname{classList}\left(\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(c\right)\right)\right)\right)\right) = \operatorname{Data}.\operatorname{T}\left(\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(c\right)\right), s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Counts/Check6.counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

For each c in Fin 84 and s in Fin 96, the integer cast of the multiplicity of s in classList c equals the matrix entry T(c,s). The source index c is embedded into Fin 96 by its value; Fin.mk omits its bound proof. These cumulative finite checks feed Certificate.transition_counts.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Counts/Check6.counts`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Counts/Check5](Check5.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data](../Data.md)
