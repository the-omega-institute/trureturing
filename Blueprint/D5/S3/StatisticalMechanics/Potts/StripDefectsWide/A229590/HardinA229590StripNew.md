# Five-row one-defect strips

## Abstract

Five-row HA arrays with exactly one equal-colour bond.

Columns have five labelled colours. The one-defect transition counts reduce to forty-one classes under colour permutations.

**Theorem 1.1 (quotient rows).**

$$\forall (b: \operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)), (\forall (s: \operatorname{Fin}\left(41\right)), (\sum_{c: \operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)} ((\operatorname{if} ((\operatorname{HardinA229590StripData}.\operatorname{cross}\left(b, \operatorname{HardinA233260Literal}.\operatorname{column}\left(c\right)\right) = 1) \land (\operatorname{HardinA233260Literal}.\operatorname{cls}\left(c\right) = s)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{HardinA229590StripData}.\operatorname{R}\left(\operatorname{HardinA233260Literal}.\operatorname{cls}\left(b\right), s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripNew.quotient_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229590: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229590>.

*Commentary.*

Exactly one monochromatic bond is added across this pair of adjacent columns. Colour permutations preserve that event and the successor class.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripNew.quotient_rows`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripData](HardinA229590StripData.md)
