# Five-row two-defect strips

## Abstract

Five-row HA arrays with exactly two equal-colour bonds.

This segment evaluates suffix indices 12 through 15.

**Theorem 1.1 (rows).**

$$\forall (k: \operatorname{Fin}\left(4\right)), ((\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA229590StripData}.\operatorname{R}\left(\right), \operatorname{HardinA229590StripData}.\operatorname{U}\left(\operatorname{Fin}.\operatorname{mk}\left((12) + (\operatorname{Fin}.\operatorname{val}\left(k\right))\right)\right)\right)) + (\operatorname{HardinA229698StripTables}.\operatorname{SQ}\left(\operatorname{Fin}.\operatorname{mk}\left((12) + (\operatorname{Fin}.\operatorname{val}\left(k\right))\right)\right)) = \operatorname{HardinA229698StripTables}.\operatorname{J}\left(\operatorname{Fin}.\operatorname{mk}\left((12) + (\operatorname{Fin}.\operatorname{val}\left(k\right))\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripOneInjectionGroup3.rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

These entries evaluate only the contribution to the two-defect coordinates.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripOneInjectionGroup3.rows`
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripData](../A229590/HardinA229590StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripTables](HardinA229698StripTables.md)
