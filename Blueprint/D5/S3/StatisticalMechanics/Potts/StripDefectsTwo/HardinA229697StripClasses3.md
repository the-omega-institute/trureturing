# Two-defect HA strips

## Abstract

Exact two-defect sheared square-lattice strip counts.

**Theorem 1.1 (transition_counts).**

$$\forall j: \operatorname{\mathit{Fin}}\left(14\right), (((6 \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)) \land (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) < 8)) \implies (\forall p: \operatorname{\mathit{Fin}}\left(4\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\sum_{r: \operatorname{\mathit{Fin}}\left(4\right) \to \operatorname{\mathit{Fin}}\left(3\right)} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 2) \land (\operatorname{\mathit{HardinA229697StripData}}.\operatorname{\mathit{cl}}\left(r, 2 - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = (\operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(28, j\right): \operatorname{\mathit{Fin}}\left(42\right)))) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229697StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229697StripData}}.\operatorname{\mathit{cl}}\left(p, 2\right), (\operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(28, j\right): \operatorname{\mathit{Fin}}\left(42\right))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripClasses3.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229697: two-defect canonical HA arrays*. URL: <https://oeis.org/A229697>.

*Commentary.*

Counts only the new cost-two transitions into the stated output interval. The sum runs over every actual successor column with three possible colours at each site.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripClasses3.transition_counts`
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData](../StripDefects/HardinA229589StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData](HardinA229697StripData.md)
