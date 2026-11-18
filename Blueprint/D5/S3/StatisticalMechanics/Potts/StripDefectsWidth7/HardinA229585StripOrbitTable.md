# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

Exact successor multisets share the finite enumeration across destination classes. All multiplicities retain the literal labelled-row count.

**Theorem 1.1 (All explicit output multiplicities).**

$$\forall q: \operatorname{\mathit{Fin}}\left(72\right), (\forall s: \operatorname{\mathit{Fin}}\left(72\right), (\operatorname{\mathit{Int}}.\operatorname{\mathit{ofNat}}\left(\operatorname{\mathit{Multiset}}.\operatorname{\mathit{count}}\left(s, \operatorname{\mathit{HardinA229585StripOrbit}}.\operatorname{\mathit{images}}\left(q\right)\right)\right) = \operatorname{\mathit{HardinA229585StripData}}.\operatorname{T}\left(q, s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbitTable.table_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

The multiplicity table equals the transition matrix at every input and output class.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbitTable.table_counts`
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData](HardinA229585StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbit](HardinA229585StripOrbit.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable0](TableChecks/HardinA229585StripTable0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable1](TableChecks/HardinA229585StripTable1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable2](TableChecks/HardinA229585StripTable2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable3](TableChecks/HardinA229585StripTable3.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable4](TableChecks/HardinA229585StripTable4.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable5](TableChecks/HardinA229585StripTable5.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable6](TableChecks/HardinA229585StripTable6.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable7](TableChecks/HardinA229585StripTable7.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable8](TableChecks/HardinA229585StripTable8.md)
