# Five-row two-defect strips

## Abstract

Five-row HA arrays with exactly two equal-colour bonds.

This segment advances powers 0 through 4.

**Theorem 1.1 (steps).**

$$\forall (k: \operatorname{Fin}\left(5\right)), (\operatorname{HardinA229698StripTables}.\operatorname{V}\left(\operatorname{Fin}.\operatorname{mk}\left(((0) + (\operatorname{Fin}.\operatorname{val}\left(k\right))) + (1)\right)\right) = (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA233260Literal}.\operatorname{Q}\left(\right), \operatorname{HardinA229698StripTables}.\operatorname{V}\left(\operatorname{Fin}.\operatorname{mk}\left((0) + (\operatorname{Fin}.\operatorname{val}\left(k\right))\right)\right)\right)) + (\operatorname{HardinA229698StripTables}.\operatorname{J}\left(\operatorname{Fin}.\operatorname{mk}\left((0) + (\operatorname{Fin}.\operatorname{val}\left(k\right))\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripStepGroup0.steps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

Each next vector equals Q applied to the previous vector plus the contribution from the lower-budget blocks.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripStepGroup0.steps`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripTables](HardinA229698StripTables.md)
