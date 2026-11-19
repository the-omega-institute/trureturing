# Five-row two-defect strips

## Abstract

Five-row HA arrays with exactly two equal-colour bonds.

The block structure separates the newly computed coordinates from the inherited suffix.

**Theorem 1.1 (powers table).**

$$\forall (k: \operatorname{Fin}\left(28\right)), (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA229698StripData}.\operatorname{T}\left(\right)^{\operatorname{Fin}.\operatorname{val}\left(k\right)}, \operatorname{HardinA229698StripData}.\operatorname{terminal}\left(\right)\right) = \operatorname{Sum}.\operatorname{elim}\left(\operatorname{HardinA229698StripTables}.\operatorname{V}\left(k\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA229590StripData}.\operatorname{T}\left(\right)^{\operatorname{Fin}.\operatorname{val}\left(k\right)}, \operatorname{HardinA229590StripData}.\operatorname{terminal}\left(\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripPowers.powers_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

The last 82 coordinates are the one-defect power vector. Only the first 41 coordinates are supplied by V.

**Theorem 1.2 (power polynomial).**

$$\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA229698StripData}.\operatorname{T}\left(\right)^{(6) + (21)}, \operatorname{HardinA229698StripData}.\operatorname{terminal}\left(\right)\right) = \sum_{j: \operatorname{Fin}\left(21\right)} (\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{HardinA229698StripData}.\operatorname{coefficients}\left(j\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA229698StripData}.\operatorname{T}\left(\right)^{(6) + (\operatorname{Fin}.\operatorname{val}\left(j\right))}, \operatorname{HardinA229698StripData}.\operatorname{terminal}\left(\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripPowers.power_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

The new coordinates satisfy the degree-21 relation. On the last 82 coordinates, the one-defect degree-14 polynomial is multiplied by the zero-defect degree-seven factor.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripPowers.power_polynomial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripPowers.powers_table`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripData](../A229590/HardinA229590StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripPowers](../A229590/HardinA229590StripPowers.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData](HardinA229698StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripInjection](HardinA229698StripInjection.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripStepGroup0](HardinA229698StripStepGroup0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripStepGroup1](HardinA229698StripStepGroup1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripStepGroup2](HardinA229698StripStepGroup2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripStepGroup3](HardinA229698StripStepGroup3.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripStepGroup4](HardinA229698StripStepGroup4.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripStepGroup5](HardinA229698StripStepGroup5.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripTables](HardinA229698StripTables.md)
