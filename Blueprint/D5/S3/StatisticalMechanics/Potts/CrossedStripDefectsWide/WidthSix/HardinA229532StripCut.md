# Width-six HDA transfer

## Abstract

Exact width-six HDA transfer.

**Theorem 1.1 (Structural proper-colouring cut).**

$$\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(2\right), (\forall s: \operatorname{\mathit{Fin}}\left(20\right), ((((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 1) \land (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right) < 10)) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 0) \land (10 \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right)))) \implies (((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(11, s\right): \operatorname{\mathit{Fin}}\left(31\right)))) \iff ((\operatorname{\mathit{HardinThinGraphTransport}}.\operatorname{\mathit{proper}}\left(r\right)) \land ((\operatorname{\mathit{HardinThinGraphTransport}}.\operatorname{\mathit{compatible}}\left(\operatorname{\mathit{true}}, p, r\right)) \land (\operatorname{\mathit{HardinA233172DiagonalStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), r\right) = (\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(\operatorname{\mathit{Nat}}.\operatorname{\mathit{mod}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right), 10\right) + 1\right): \operatorname{\mathit{Fin}}\left(11\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripCut.class_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229532: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229532>.

*Commentary.*

For every pair of actual rows, residual budget d : Fin 2 and target s : Fin 20 in the matching proper block, the defect predicate is equivalent to properness, crossed compatibility and the published boundary class. A sum of nonnegative bond counts vanishes precisely when every bond has distinct endpoints. Only the single-row class correspondence is checked by finite kernel evaluation. All twenty proper target-column proofs consume this common equivalence and the original scanner successor counts. Nat.mod is natural-number modulo, the nonnegative remainder.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripCut.class_cut`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip](../../../../Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport](../../../../Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripData](HardinA229532StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData](../../StripDefects/HardinA229584StripData.md)
