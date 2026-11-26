# Width-six source transitions

## Abstract

Exact successor multisets at canonical boundary states.

For the source indices in the displayed range, the sorted list of admissible labelled successors, mapped to their residual-budget classes, equals the class list selected by the source class. Repeated class entries record successor multiplicities.

**Theorem 1.1 (Source states 0 through 137).**

$$\forall (i: \operatorname{Fin}\left(138\right)), (\operatorname{Data}.\operatorname{successors}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Sources}.\operatorname{sources}\left(\operatorname{Fin}.\operatorname{mk}\left(0+\operatorname{Fin}.\operatorname{val}\left(i\right)\right)\right)\right), \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Sources}.\operatorname{sources}\left(\operatorname{Fin}.\operatorname{mk}\left(0+\operatorname{Fin}.\operatorname{val}\left(i\right)\right)\right)\right)\right)\right) = \operatorname{Data}.\operatorname{classList}\left(\operatorname{Data}.\operatorname{cl}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Sources}.\operatorname{sources}\left(\operatorname{Fin}.\operatorname{mk}\left(0+\operatorname{Fin}.\operatorname{val}\left(i\right)\right)\right)\right), \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Sources}.\operatorname{sources}\left(\operatorname{Fin}.\operatorname{mk}\left(0+\operatorname{Fin}.\operatorname{val}\left(i\right)\right)\right)\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Chunks0/Source23.successor_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The source table supplies a canonical row and residual budget. Every admissible labelled next row contributes its new class, including multiplicity; sorting gives the class list. These identities determine the quotient transfer.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Chunks0/Source23.successor_rows`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Chunks0/Source22](Source22.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data](../Data.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Sources](../Sources.md)
