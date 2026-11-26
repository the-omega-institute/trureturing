# Width-six transfer identities

## Abstract

Coordinate identities for width-six king transfers.

**Theorem 1.1 (Check5).**

$$(\forall (i: \operatorname{Fin}\left(11\right)), (\forall (s: \operatorname{Fin}\left(72\right)), (\operatorname{Data}.\operatorname{W}\left(\operatorname{Fin}.\operatorname{succ}\left(i\right), \operatorname{Fin}.\operatorname{mk}\left((0) + (\operatorname{Fin}.\operatorname{val}\left(s\right))\right)\right) = \operatorname{Matrix}.\operatorname{vecMul}\left(\operatorname{Data}.\operatorname{W}\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right), \operatorname{Data}.\operatorname{T}, \operatorname{Fin}.\operatorname{mk}\left((0) + (\operatorname{Fin}.\operatorname{val}\left(s\right))\right)\right)))) \land (\forall (s: \operatorname{Fin}\left(72\right)), (\operatorname{Data}.\operatorname{W}\left(11, \operatorname{Fin}.\operatorname{mk}\left((0) + (\operatorname{Fin}.\operatorname{val}\left(s\right))\right)\right) = \sum_{(j: \operatorname{Fin}\left(6\right))} (\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Matrix}.\operatorname{vecCons}\left(-8, \operatorname{Matrix}.\operatorname{vecCons}\left(36, \operatorname{Matrix}.\operatorname{vecCons}\left(-66, \operatorname{Matrix}.\operatorname{vecCons}\left(63, \operatorname{Matrix}.\operatorname{vecCons}\left(-33, \operatorname{Matrix}.\operatorname{vecCons}\left(9, \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right)\right)\left(j\right), \operatorname{Data}.\operatorname{W}\left(\operatorname{Fin}.\operatorname{mk}\left((5) + (\operatorname{Fin}.\operatorname{val}\left(j\right))\right), \operatorname{Fin}.\operatorname{mk}\left((0) + (\operatorname{Fin}.\operatorname{val}\left(s\right))\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Krylov/Check5.certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

At the accumulated prefix coordinates the eleven forward steps follow matrix multiplication, and the order-six polynomial annihilates the shifted forward vectors.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Krylov/Check5.certificate`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data](../Data.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Krylov/Check4](Check4.md)
