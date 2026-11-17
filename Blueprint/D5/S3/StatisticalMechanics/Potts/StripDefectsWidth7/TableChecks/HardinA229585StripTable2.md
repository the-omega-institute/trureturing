# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

Exact successor multisets share the finite enumeration across destination classes. All multiplicities retain the literal labelled-row count.

**Theorem 1.1 (Output multiplicities on an input interval).**

$$\forall q: \operatorname{\mathit{Fin}}\left(72\right), (((16 \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(q\right)) \land (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(q\right) < 24)) \implies (\forall s: \operatorname{\mathit{Fin}}\left(72\right), (\operatorname{\mathit{Int}}.\operatorname{\mathit{ofNat}}\left(\operatorname{\mathit{Multiset}}.\operatorname{\mathit{count}}\left(s, \operatorname{\mathit{HardinA229585StripOrbit}}.\operatorname{\mathit{images}}\left(q\right)\right)\right) = \operatorname{\mathit{HardinA229585StripData}}.\operatorname{T}\left(q, s\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable2.table_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

Each input in this interval has all 72 output multiplicities verified.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable2.table_counts`
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData](../HardinA229585StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbit](../HardinA229585StripOrbit.md)
