# Two-defect HA strips

## Abstract

Exact two-defect sheared square-lattice strip counts.

**Theorem 1.1 (leading_counts).**

$$\forall p: \operatorname{\mathit{Fin}}\left(3\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(3\right), (\forall j: \operatorname{\mathit{Fin}}\left(10\right), (\sum_{r: \operatorname{\mathit{Fin}}\left(3\right) \to \operatorname{\mathit{Fin}}\left(3\right)} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229696StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(5, j\right): \operatorname{\mathit{Fin}}\left(15\right)))) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229696StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229696StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(5, j\right): \operatorname{\mathit{Fin}}\left(15\right))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripCut.leading_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229696: two-defect canonical HA arrays*. URL: <https://oeis.org/A229696>.

*Commentary.*

The two leading sectors call the frozen one-defect transition theorem after a single-column arithmetic cut. At zero residual budget these targets are unreachable.

**Theorem 1.2 (tail_counts).**

$$\forall p: \operatorname{\mathit{Fin}}\left(3\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(2\right), (\forall j: \operatorname{\mathit{Fin}}\left(5\right), (\sum_{r: \operatorname{\mathit{Fin}}\left(3\right) \to \operatorname{\mathit{Fin}}\left(3\right)} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229696StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = (\operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(10, j\right): \operatorname{\mathit{Fin}}\left(15\right)))) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229696StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229696StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), (\operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(10, j\right): \operatorname{\mathit{Fin}}\left(15\right))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripCut.tail_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229696: two-defect canonical HA arrays*. URL: <https://oeis.org/A229696>.

*Commentary.*

Budgets zero and one call the frozen final-sector transition theorem. Numeric cuts quantify one column and the small cost, rather than all pairs of columns.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripCut.leading_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripCut.tail_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer](../../../Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229588Strip](../StripDefects/HardinA229588Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData](HardinA229696StripData.md)
