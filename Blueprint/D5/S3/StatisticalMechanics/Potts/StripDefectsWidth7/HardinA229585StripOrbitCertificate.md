# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

Exact successor multisets share the finite enumeration across destination classes. All multiplicities retain the literal labelled-row count.

**Theorem 1.1 (Canonical exact transition histogram).**

$$\forall p: \mathit{Boundary}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies ((\operatorname{\mathit{HardinA233177Canonical}}.\operatorname{\mathit{Canonical}}\left(p\right)) \implies (\forall s: \operatorname{\mathit{Fin}}\left(72\right), (\sum_{r: \mathit{Row}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229585StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), s\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbitCertificate.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

The multiset certificate and its multiplicity table reconstruct the complete original sum over all labelled rows.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbitCertificate.transition_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData](HardinA229585StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbit](HardinA229585StripOrbit.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbitTable](HardinA229585StripOrbitTable.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/OrbitChecks/HardinA229585StripOrbit0](OrbitChecks/HardinA229585StripOrbit0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/OrbitChecks/HardinA229585StripOrbit1](OrbitChecks/HardinA229585StripOrbit1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/OrbitChecks/HardinA229585StripOrbit2](OrbitChecks/HardinA229585StripOrbit2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/OrbitChecks/HardinA229585StripOrbit3](OrbitChecks/HardinA229585StripOrbit3.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/OrbitChecks/HardinA229585StripOrbit4](OrbitChecks/HardinA229585StripOrbit4.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/OrbitChecks/HardinA229585StripOrbit5](OrbitChecks/HardinA229585StripOrbit5.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/OrbitChecks/HardinA229585StripOrbit6](OrbitChecks/HardinA229585StripOrbit6.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/OrbitChecks/HardinA229585StripOrbit7](OrbitChecks/HardinA229585StripOrbit7.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/OrbitChecks/HardinA229585StripOrbit8](OrbitChecks/HardinA229585StripOrbit8.md)
