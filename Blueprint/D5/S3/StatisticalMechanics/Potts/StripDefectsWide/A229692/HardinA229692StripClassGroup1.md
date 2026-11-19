# Two-defect HA strips

## Abstract

Exact two-defect six-column sheared square-lattice counts.

**Theorem 1.1 (transition_counts6).**

$$\forall p: \operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies ((\operatorname{\mathit{HardinA233177Canonical}}.\operatorname{\mathit{Canonical}}\left(p\right)) \implies ((\neg((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) \le 1) \land (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)))) \implies (\sum_{r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right)} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = (38: \operatorname{\mathit{Fin}}\left(68\right)))) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229692StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), (38: \operatorname{\mathit{Fin}}\left(68\right))\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup1.transition_counts6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229692: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229692>.

*Commentary.*

Only new-sector canonical boundaries are enumerated; the old valid domain is excluded by the explicit hypothesis.

**Theorem 1.2 (transition_counts7).**

$$\forall p: \operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies ((\operatorname{\mathit{HardinA233177Canonical}}.\operatorname{\mathit{Canonical}}\left(p\right)) \implies ((\neg((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) \le 1) \land (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)))) \implies (\sum_{r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right)} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = (39: \operatorname{\mathit{Fin}}\left(68\right)))) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229692StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), (39: \operatorname{\mathit{Fin}}\left(68\right))\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup1.transition_counts7` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229692: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229692>.

*Commentary.*

Only new-sector canonical boundaries are enumerated; the old valid domain is excluded by the explicit hypothesis.

**Theorem 1.3 (transition_counts8).**

$$\forall p: \operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies ((\operatorname{\mathit{HardinA233177Canonical}}.\operatorname{\mathit{Canonical}}\left(p\right)) \implies ((\neg((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) \le 1) \land (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)))) \implies (\sum_{r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right)} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = (40: \operatorname{\mathit{Fin}}\left(68\right)))) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229692StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), (40: \operatorname{\mathit{Fin}}\left(68\right))\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup1.transition_counts8` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229692: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229692>.

*Commentary.*

Only new-sector canonical boundaries are enumerated; the old valid domain is excluded by the explicit hypothesis.

**Theorem 1.4 (transition_counts9).**

$$\forall p: \operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies ((\operatorname{\mathit{HardinA233177Canonical}}.\operatorname{\mathit{Canonical}}\left(p\right)) \implies ((\neg((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) \le 1) \land (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)))) \implies (\sum_{r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right)} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = (41: \operatorname{\mathit{Fin}}\left(68\right)))) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229692StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), (41: \operatorname{\mathit{Fin}}\left(68\right))\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup1.transition_counts9` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229692: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229692>.

*Commentary.*

Only new-sector canonical boundaries are enumerated; the old valid domain is excluded by the explicit hypothesis.

**Theorem 1.5 (transition_counts10).**

$$\forall p: \operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies ((\operatorname{\mathit{HardinA233177Canonical}}.\operatorname{\mathit{Canonical}}\left(p\right)) \implies ((\neg((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) \le 1) \land (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)))) \implies (\sum_{r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right)} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = (42: \operatorname{\mathit{Fin}}\left(68\right)))) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229692StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), (42: \operatorname{\mathit{Fin}}\left(68\right))\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup1.transition_counts10` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229692: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229692>.

*Commentary.*

Only new-sector canonical boundaries are enumerated; the old valid domain is excluded by the explicit hypothesis.

**Theorem 1.6 (transition_counts11).**

$$\forall p: \operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies ((\operatorname{\mathit{HardinA233177Canonical}}.\operatorname{\mathit{Canonical}}\left(p\right)) \implies ((\neg((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) \le 1) \land (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)))) \implies (\sum_{r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right)} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = (43: \operatorname{\mathit{Fin}}\left(68\right)))) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229692StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), (43: \operatorname{\mathit{Fin}}\left(68\right))\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup1.transition_counts11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229692: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229692>.

*Commentary.*

Only new-sector canonical boundaries are enumerated; the old valid domain is excluded by the explicit hypothesis.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup1.transition_counts10`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup1.transition_counts11`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup1.transition_counts6`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup1.transition_counts7`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup1.transition_counts8`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup1.transition_counts9`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData](../../StripDefects/HardinA229584StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripData](../HardinA229692StripData.md)
