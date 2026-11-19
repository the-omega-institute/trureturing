# Five-row one-defect strips

## Abstract

Five-row HA arrays with exactly one equal-colour bond.

Only vectors multiplied by the one-defect matrix R occur here; the zero-defect table and its polynomial are those of the five-row quotient.

**Theorem 1.1 (injection powers).**

$$\forall (k: \operatorname{Fin}\left(18\right)), (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA229590StripData}.\operatorname{R}\left(\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA233260Literal}.\operatorname{Q}\left(\right)^{\operatorname{Fin}.\operatorname{val}\left(k\right)}, (1: \operatorname{Fin}\left(41\right) \to \operatorname{Int})\right)\right) = \operatorname{HardinA229590StripData}.\operatorname{RU}\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripInjection.injection_powers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229590: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229590>.

*Commentary.*

Applying R to the old powers counts a single newly spent defect followed by a proper suffix. The old vector polynomial propagates this relation to later steps.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripInjection.injection_powers`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](../../../../Combinatorics/TraceAvoidingArrays/TransferMatrix.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripData](HardinA229590StripData.md)
