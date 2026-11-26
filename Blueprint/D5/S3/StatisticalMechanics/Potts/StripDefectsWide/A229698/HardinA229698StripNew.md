# Five-row two-defect strips

## Abstract

Five-row HA arrays with exactly two equal-colour bonds.

The quotient by colour permutations has 41 classes.

**Theorem 1.1 (quotient rows).**

$$\forall (b: \operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)), (\forall (s: \operatorname{Fin}\left(41\right)), (\sum_{c: \operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)} ((\operatorname{if} ((\operatorname{HardinA229590StripData}.\operatorname{cross}\left(b, \operatorname{HardinA233260Literal}.\operatorname{column}\left(c\right)\right) = 2) \land (\operatorname{HardinA233260Literal}.\operatorname{cls}\left(c\right) = s)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{HardinA229698StripData}.\operatorname{S}\left(\operatorname{HardinA233260Literal}.\operatorname{cls}\left(b\right), s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripNew.quotient_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

Colour permutations preserve the number of monochromatic bonds and the successor class.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripNew.quotient_rows`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripData](../A229590/HardinA229590StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripNew](../A229590/HardinA229590StripNew.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripClassGroup0](HardinA229698StripClassGroup0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripClassGroup1](HardinA229698StripClassGroup1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripClassGroup2](HardinA229698StripClassGroup2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripClassGroup3](HardinA229698StripClassGroup3.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripClassGroup4](HardinA229698StripClassGroup4.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripClassGroup5](HardinA229698StripClassGroup5.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripClassGroup6](HardinA229698StripClassGroup6.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData](HardinA229698StripData.md)
