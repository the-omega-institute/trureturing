# Width-five HDA transfer

## Abstract

Exact width-five HDA transfer.

**Theorem 1.1 (All target classes).**

$$\forall p: \operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229634StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall s: \operatorname{\mathit{Fin}}\left(33\right), (\sum_{r: \operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right)} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229634StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = s)) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)): \operatorname{\mathit{Int}})) = \operatorname{\mathit{HardinA229634StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229634StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), s\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClasses.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

For every actual row p, residual d : Fin 3 and target s : Fin 33, Valid p (Fin.val d) implies that the actual permitted successor sum is T (cl p (Fin.val d)) s. The proof transports a canonical representative back by a colour permutation; every new target case applies its checked canonical-row theorem; the final recurrence consumes the combined identity.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClasses.transition_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip](../../../Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](../../../Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip](../../../Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData](../CrossedStripDefects/HardinA229531StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass0](HardinA229634StripClass0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass1](HardinA229634StripClass1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass10](HardinA229634StripClass10.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass11](HardinA229634StripClass11.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass12](HardinA229634StripClass12.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass2](HardinA229634StripClass2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass3](HardinA229634StripClass3.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass4](HardinA229634StripClass4.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass5](HardinA229634StripClass5.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass6](HardinA229634StripClass6.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass7](HardinA229634StripClass7.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass8](HardinA229634StripClass8.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass9](HardinA229634StripClass9.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripCut](HardinA229634StripCut.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData](HardinA229634StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
