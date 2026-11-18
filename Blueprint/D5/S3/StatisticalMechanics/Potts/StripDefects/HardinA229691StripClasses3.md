# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

Exactly 2 monochromatic bonds are allowed. These are unsatisfied bonds of the three-state Potts antiferromagnet; the theorem concerns finite combinatorial counts.

**Theorem 1.1 (Output-class transition sums).**

$$\forall s: \operatorname{\mathit{Fin}}\left(27\right), (((6 \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right)) \land (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right) < 8)) \implies (\forall p: \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\sum_{r: \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Row}}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229691StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), s\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses3.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229691: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229691>.

*Commentary.*

The indicated class interval is checked over every admissible boundary and budget.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses3.transition_counts`
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData](HardinA229583StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData](HardinA229691StripData.md)
