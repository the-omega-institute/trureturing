# Width-six source transitions

## Abstract

Exact successor multisets at canonical boundary states.

The finite certificate establishes the domain successor multiset and its labelled-row multiplicities. These transition facts supply content for the later transfer proof.

**Theorem 1.1 (Source states 0 through 23).**

$$\forall (i: \operatorname{Fin}\left(24\right)), (\operatorname{Data}.\operatorname{successors}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Sources}.\operatorname{sources}\left(\operatorname{Fin}.\operatorname{mk}\left(0+\operatorname{Fin}.\operatorname{val}\left(i\right)\right)\right)\right), \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Sources}.\operatorname{sources}\left(\operatorname{Fin}.\operatorname{mk}\left(0+\operatorname{Fin}.\operatorname{val}\left(i\right)\right)\right)\right)\right)\right) = \operatorname{Data}.\operatorname{classList}\left(\operatorname{Data}.\operatorname{cl}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Sources}.\operatorname{sources}\left(\operatorname{Fin}.\operatorname{mk}\left(0+\operatorname{Fin}.\operatorname{val}\left(i\right)\right)\right)\right), \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Sources}.\operatorname{sources}\left(\operatorname{Fin}.\operatorname{mk}\left(0+\operatorname{Fin}.\operatorname{val}\left(i\right)\right)\right)\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Chunks0/Source7.successor_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

The source table supplies a canonical row and residual budget. Every admissible labelled next row contributes its new class, including multiplicity; sorting gives the class list. These identities determine the quotient transfer.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Chunks0/Source7.successor_rows`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Chunks0/Source6](Source6.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data](../Data.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Sources](../Sources.md)
