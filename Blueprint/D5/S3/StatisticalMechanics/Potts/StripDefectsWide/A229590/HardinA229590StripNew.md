# Five-row one-defect strips

## Abstract

Five-row HA arrays with exactly one equal-colour bond.

Columns have five labelled colours. The one-defect transition counts reduce to forty-one classes under colour permutations.

**Theorem 1.1 (cross relabel).**

$$\forall (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right)), (\forall (a: \operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)), (\forall (b: \operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)), (\operatorname{HardinA229590StripData}.\operatorname{cross}\left(\operatorname{HardinA233260Literal}.\operatorname{relabel}\left(e, a\right), \operatorname{HardinA233260Literal}.\operatorname{column}\left(\operatorname{HardinA233260Literal}.\operatorname{relabel}\left(e, b\right)\right)\right) = \operatorname{HardinA229590StripData}.\operatorname{cross}\left(a, \operatorname{HardinA233260Literal}.\operatorname{column}\left(b\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripNew.cross_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229590: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229590>.

*Commentary.*

The same permutation of the three colours preserves all equal-colour bonds.

**Theorem 1.2 (quotient rows).**

$$\forall (b: \operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)), (\forall (s: \operatorname{Fin}\left(41\right)), (\sum_{c: \operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)} ((\operatorname{if} ((\operatorname{HardinA229590StripData}.\operatorname{cross}\left(b, \operatorname{HardinA233260Literal}.\operatorname{column}\left(c\right)\right) = 1) \land (\operatorname{HardinA233260Literal}.\operatorname{cls}\left(c\right) = s)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{HardinA229590StripData}.\operatorname{R}\left(\operatorname{HardinA233260Literal}.\operatorname{cls}\left(b\right), s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripNew.quotient_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229590: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229590>.

*Commentary.*

Exactly one monochromatic bond is added across this pair of adjacent columns. Colour permutations preserve that event and the successor class.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripNew.cross_relabel`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripNew.quotient_rows`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripData](HardinA229590StripData.md)
