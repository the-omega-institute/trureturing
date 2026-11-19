# Five-row two-defect strips

## Abstract

Five-row HA arrays with exactly two equal-colour bonds.

Budget subtraction determines which of the three blocks contains a successor.

**Theorem 1.1 (transition counts).**

$$\forall (p: \operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)), (\forall (d: \operatorname{Fin}\left(3\right)), (\forall (s: \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Fin}\left(41\right)\right)\right)), (\sum_{r: \operatorname{Fin}\left(5\right) \to \operatorname{Fin}\left(3\right)} ((\operatorname{if} ((\operatorname{HardinA229590StripData}.\operatorname{cross}\left(p, r\right) \le \operatorname{Fin}.\operatorname{val}\left(d\right)) \land (\operatorname{HardinA229698StripData}.\operatorname{cl}\left(\operatorname{HardinA229590StripData}.\operatorname{boundary}\left(r\right), (\operatorname{Fin}.\operatorname{val}\left(d\right)) - (\operatorname{HardinA229590StripData}.\operatorname{cross}\left(p, r\right))\right) = s)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{HardinA229698StripData}.\operatorname{T}\left(\operatorname{HardinA229698StripData}.\operatorname{cl}\left(p, \operatorname{Fin}.\operatorname{val}\left(d\right)\right), s\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripCut.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

A cost-zero step preserves the budget; costs one and two spend the corresponding amount. Every lower-budget transition is inherited from the one-defect count.

**Theorem 1.2 (initial counts).**

$$\forall (s: \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Fin}\left(41\right)\right)\right)), (\sum_{r: \operatorname{Fin}\left(5\right) \to \operatorname{Fin}\left(3\right)} ((\operatorname{if} (\operatorname{HardinA229698StripData}.\operatorname{cl}\left(\operatorname{HardinA229590StripData}.\operatorname{boundary}\left(r\right), 2\right) = s) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{HardinA229698StripData}.\operatorname{initial}\left(s\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripCut.initial_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

The initial multiplicities are inherited from the one-defect classes with their remaining budget shifted by one.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripCut.initial_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripCut.transition_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripCut](../A229590/HardinA229590StripCut.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripData](../A229590/HardinA229590StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripNew](../A229590/HardinA229590StripNew.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData](HardinA229698StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripNew](HardinA229698StripNew.md)
