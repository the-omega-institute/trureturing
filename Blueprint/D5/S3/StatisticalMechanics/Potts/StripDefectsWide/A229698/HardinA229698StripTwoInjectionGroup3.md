# Five-row two-defect strips

## Abstract

Five-row HA arrays with exactly two equal-colour bonds.

This segment evaluates suffix indices 9 through 11.

**Theorem 1.1 (rows).**

$$\forall (k: \operatorname{Fin}\left(3\right)), (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA229698StripData}.\operatorname{S}\left(\right), \operatorname{HardinA233260Literal}.\operatorname{W}\left(\operatorname{Fin}.\operatorname{mk}\left((9) + (\operatorname{Fin}.\operatorname{val}\left(k\right))\right)\right)\right) = \operatorname{HardinA229698StripTables}.\operatorname{SQ}\left(\operatorname{Fin}.\operatorname{mk}\left((9) + (\operatorname{Fin}.\operatorname{val}\left(k\right))\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripTwoInjectionGroup3.rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

These entries evaluate only the contribution to the two-defect coordinates.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripTwoInjectionGroup3.rows`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData](HardinA229698StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripTables](HardinA229698StripTables.md)
