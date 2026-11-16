# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

Exact successor multisets share the finite enumeration across destination classes. All multiplicities retain the literal labelled-row count.

**Definition 1.1 (Exact successor-class multiset).**

$$\forall p: \mathit{Boundary}, (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229585StripOrbit}}.\operatorname{\mathit{nextClasses}}\left(p, d\right) = \sum_{r: \mathit{Row}} ((\operatorname{\mathit{if}} (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le d) \operatorname{\mathit{then}} \operatorname{\mathit{Singleton}}.\operatorname{\mathit{singleton}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{boundary}}\left(r\right), d - \left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right)\right) \operatorname{\mathit{else}} 0))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbit.nextClasses` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

Every permitted row contributes its destination class once; disallowed rows contribute the empty multiset.

**Definition 1.2 (Successor multisets).**

$$\operatorname{\mathit{HardinA229585StripOrbit}}.\operatorname{\mathit{images}}: (\operatorname{\mathit{Fin}}\left(72\right)) \to (\operatorname{\mathit{Multiset}}\left(\operatorname{\mathit{Fin}}\left(72\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbit.images` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

The table has 72 multisets in cl index order, each containing destination indices in Fin 72 with their successor multiplicities. For source classes below 16, the destinations below 16 are generated from HardinA233255Recurrence.table: each j contributes table i j converted to a natural multiplicity via Multiset.replicate, using Fin.castAdd 56 for the inclusion. Only destinations at least 16 are retained as a literal tail. For sources zeroBudgetClass i, the complete multiset is generated from the same owner row through HardinA229585StripData.zeroBudgetClass on the destination index. The other rows retain their finite lists. The OrbitChecks.canonical_next theorems identify images with nextClasses on each valid class interval, and HardinA229585StripOrbitTable.table_counts pins each destination multiplicity to the corresponding entry of T.

**Theorem 1.3 (Histogram as a multiset multiplicity).**

$$\forall p: \mathit{Boundary}, (\forall d: \mathit{Nat}, (\forall s: \operatorname{\mathit{Fin}}\left(72\right), (\sum_{r: \mathit{Row}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le d) \land (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{boundary}}\left(r\right), d - \left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{Int}}.\operatorname{\mathit{ofNat}}\left(\operatorname{\mathit{Multiset}}.\operatorname{\mathit{count}}\left(s, \operatorname{\mathit{HardinA229585StripOrbit}}.\operatorname{\mathit{nextClasses}}\left(p, d\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbit.sum_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

Counting one selected class commutes with the finite sum of singleton contributions.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbit.images`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbit.nextClasses`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbit.sum_count`
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData](HardinA229585StripData.md)
