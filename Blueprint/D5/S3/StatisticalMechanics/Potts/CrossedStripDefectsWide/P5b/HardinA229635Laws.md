# Boundary-state laws

## Abstract

Canonical row reconstruction and terminal acceptance in the inherited block.

**Theorem 1.1 (Recovery of the canonical row).**

$$\forall p: \operatorname{\mathit{Row}}, ((\operatorname{\mathit{Canonical}}\left(p\right)) \implies ((\operatorname{h}\left(p\right) \le 2) \implies (\operatorname{\mathit{rep}}\left(\operatorname{\mathit{fresh}}\left(p\right)\right) = p)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Laws.representatives_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

A canonical row with at most two horizontal defects is reconstructed by the index of its equality pattern.

**Theorem 1.2 (Acceptance on the inherited block).**

$$\forall p: \operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{h}\left(p\right) + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) \le 1) \implies (\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{terminal}}\left(\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)\right) = (\operatorname{\mathit{if}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 0 \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Laws.old_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

A row and budget in the one-defect sector retain the inherited terminal weight.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Laws.old_terminal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Laws.representatives_complete`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State](HardinA229635State.md)
