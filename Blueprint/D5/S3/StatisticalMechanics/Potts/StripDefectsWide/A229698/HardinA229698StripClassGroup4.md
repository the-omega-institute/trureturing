# Five-row two-defect strips

## Abstract

Five-row HA arrays with exactly two equal-colour bonds.

These rows use representative indices 24 through 29.

**Theorem 1.1 (representative rows).**

$$\forall (i: \operatorname{Fin}\left(6\right)), (\forall (s: \operatorname{Fin}\left(41\right)), (\sum_{c: \operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)} ((\operatorname{if} ((\operatorname{HardinA229590StripData}.\operatorname{cross}\left(\operatorname{HardinA233260Literal}.\operatorname{representatives}\left(\operatorname{Fin}.\operatorname{mk}\left((24) + (\operatorname{Fin}.\operatorname{val}\left(i\right))\right)\right), \operatorname{HardinA233260Literal}.\operatorname{column}\left(c\right)\right) = 2) \land (\operatorname{HardinA233260Literal}.\operatorname{cls}\left(c\right) = s)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{HardinA229698StripData}.\operatorname{S}\left(\operatorname{Fin}.\operatorname{mk}\left((24) + (\operatorname{Fin}.\operatorname{val}\left(i\right))\right), s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripClassGroup4.representative_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

The displayed row counts precisely the labelled successor columns in each output colour class.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripClassGroup4.representative_rows`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripData](../A229590/HardinA229590StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData](HardinA229698StripData.md)
