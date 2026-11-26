# Five-row two-defect strips

## Abstract

Five-row HA arrays with exactly two equal-colour bonds.

The off-diagonal block acts only on suffix vectors supplied by the one-defect and zero-defect matrices.

**Theorem 1.1 (two injection powers).**

$$\forall (k: \operatorname{Fin}\left(19\right)), (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA229698StripData}.\operatorname{S}\left(\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA233260Literal}.\operatorname{Q}\left(\right)^{\operatorname{Fin}.\operatorname{val}\left(k\right)}, (1: \operatorname{Fin}\left(41\right) \to \operatorname{Int})\right)\right) = \operatorname{HardinA229698StripTables}.\operatorname{SQ}\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripInjection.two_injection_powers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

The zero-defect polynomial extends the directly computed first twelve injection vectors.

**Theorem 1.2 (injection powers).**

$$\forall (k: \operatorname{Fin}\left(27\right)), (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA229698StripData}.\operatorname{B}\left(\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA229590StripData}.\operatorname{T}\left(\right)^{\operatorname{Fin}.\operatorname{val}\left(k\right)}, \operatorname{HardinA229590StripData}.\operatorname{terminal}\left(\right)\right)\right) = \operatorname{HardinA229698StripTables}.\operatorname{J}\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripInjection.injection_powers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

The one-defect polynomial extends the injection vectors beyond its existing power table.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripInjection.injection_powers`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripInjection.two_injection_powers`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](../../../../Combinatorics/TraceAvoidingArrays/TransferMatrix.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripData](../A229590/HardinA229590StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripPowers](../A229590/HardinA229590StripPowers.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData](HardinA229698StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripOneInjectionGroup0](HardinA229698StripOneInjectionGroup0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripOneInjectionGroup1](HardinA229698StripOneInjectionGroup1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripOneInjectionGroup2](HardinA229698StripOneInjectionGroup2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripOneInjectionGroup3](HardinA229698StripOneInjectionGroup3.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripOneInjectionGroup4](HardinA229698StripOneInjectionGroup4.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripTables](HardinA229698StripTables.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripTwoInjectionGroup0](HardinA229698StripTwoInjectionGroup0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripTwoInjectionGroup1](HardinA229698StripTwoInjectionGroup1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripTwoInjectionGroup2](HardinA229698StripTwoInjectionGroup2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripTwoInjectionGroup3](HardinA229698StripTwoInjectionGroup3.md)
