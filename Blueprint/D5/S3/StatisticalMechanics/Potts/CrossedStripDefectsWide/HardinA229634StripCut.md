# Width-five two-defect transfer

## Abstract

Exact-budget HDA extension.

**Theorem 1.1 (Inherited active-sector cut).**

$$\forall p: \operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall r: \operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(3\right), (\forall j: \operatorname{\mathit{Fin}}\left(20\right), ((0 < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \implies (((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229634StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(13, j\right): \operatorname{\mathit{Fin}}\left(33\right)))) \iff ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - 1) \land (\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - 1 - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = j)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripCut.active_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

For a positive residual, a transition into the inherited twenty classes is precisely an original one-defect transition with one less unit of residual budget. The proof checks only single-row arithmetic class facts, then handles arbitrary bond costs structurally.

**Theorem 1.2 (Inherited successor counts).**

$$\forall p: \operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229634StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall j: \operatorname{\mathit{Fin}}\left(20\right), (\sum_{r: \operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right)} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229634StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(13, j\right): \operatorname{\mathit{Fin}}\left(33\right)))) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)): \operatorname{\mathit{Int}})) = \operatorname{\mathit{HardinA229634StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229634StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(13, j\right): \operatorname{\mathit{Fin}}\left(33\right))\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripCut.inherited_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

Every inherited column applies HardinA229531StripClasses.transition_counts through active_cut. At zero residual its sum and matrix block are both zero.

**Theorem 1.3 (Proper terminal-sector cut).**

$$\forall p: \operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall r: \operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall j: \operatorname{\mathit{Fin}}\left(6\right), (((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 0) \land (\operatorname{\mathit{HardinA229634StripData}}.\operatorname{\mathit{cl}}\left(r, 0 - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = (\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(20 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right): \operatorname{\mathit{Fin}}\left(33\right)))) \iff ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 0) \land (\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{cl}}\left(r, 0 - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = (\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(6 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right): \operatorname{\mathit{Fin}}\left(20\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripCut.zero_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

For zero residual and one of the six proper targets, the new predicate is the original terminal proper predicate with indices shifted from six to twenty. No enumeration of row pairs is used.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripCut.active_cut`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripCut.inherited_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripCut.zero_cut`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripClasses](../CrossedStripDefects/HardinA229531StripClasses.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData](HardinA229634StripData.md)
