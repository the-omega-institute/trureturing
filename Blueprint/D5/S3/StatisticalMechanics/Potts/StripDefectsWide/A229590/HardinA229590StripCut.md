# Five-row one-defect strips

## Abstract

Five-row HA arrays with exactly one equal-colour bond.

The two summands retain the exact remaining budget. The terminal summand represents zero remaining defects.

**Theorem 1.1 (column boundary).**

$$\forall (r: \operatorname{Fin}\left(5\right) \to \operatorname{Fin}\left(3\right)), (\operatorname{HardinA233260Literal}.\operatorname{column}\left(\operatorname{HardinA229590StripData}.\operatorname{boundary}\left(r\right)\right) = r)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripCut.column_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229590: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229590>.

*Commentary.*

column boundary.

**Theorem 1.2 (transition counts).**

$$\forall (p: \operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)), (\forall (d: \operatorname{Fin}\left(2\right)), (\forall (s: \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Fin}\left(41\right)\right)), (\sum_{r: \operatorname{Fin}\left(5\right) \to \operatorname{Fin}\left(3\right)} ((\operatorname{if} ((\operatorname{HardinA229590StripData}.\operatorname{cross}\left(p, r\right) \le \operatorname{Fin}.\operatorname{val}\left(d\right)) \land (\operatorname{HardinA229590StripData}.\operatorname{cl}\left(\operatorname{HardinA229590StripData}.\operatorname{boundary}\left(r\right), (\operatorname{Fin}.\operatorname{val}\left(d\right)) - (\operatorname{HardinA229590StripData}.\operatorname{cross}\left(p, r\right))\right) = s)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{HardinA229590StripData}.\operatorname{T}\left(\operatorname{HardinA229590StripData}.\operatorname{cl}\left(p, \operatorname{Fin}.\operatorname{val}\left(d\right)\right), s\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripCut.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229590: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229590>.

*Commentary.*

A zero-cost step preserves the remaining budget and uses Q; a step of cost one spends the budget and uses R. No other step is accepted.

**Theorem 1.3 (initial counts).**

$$\forall (s: \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Fin}\left(41\right)\right)), (\sum_{r: \operatorname{Fin}\left(5\right) \to \operatorname{Fin}\left(3\right)} ((\operatorname{if} (\operatorname{HardinA229590StripData}.\operatorname{cl}\left(\operatorname{HardinA229590StripData}.\operatorname{boundary}\left(r\right), 1\right) = s) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{HardinA229590StripData}.\operatorname{initial}\left(s\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripCut.initial_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229590: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229590>.

*Commentary.*

Every initial column starts with one remaining defect. The class multiplicities are the five-row multiplicities.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripCut.column_boundary`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripCut.initial_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripCut.transition_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip](../../../../Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip](../../../../Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripData](HardinA229590StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripNew](HardinA229590StripNew.md)
