# The exact integer transfer

## Abstract

Transition, initial and terminal weights for the 127-state transfer.

**Definition 1.1 (The 127-state transfer matrix).**

$$\forall i: \operatorname{\mathit{State}}, (\forall j: \operatorname{\mathit{State}}, (\operatorname{T}\left(i, j\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{addCases}}\left(\lambda k: \operatorname{\mathit{Fin}}\left(31\right) \mapsto (\operatorname{\mathit{Fin}}.\operatorname{\mathit{addCases}}\left(\operatorname{\mathit{HardinA229532StripData}}.\operatorname{T}\left(k\right), \lambda l: \operatorname{\mathit{Fresh}} \mapsto (0), j\right)), \lambda l: \operatorname{\mathit{Fresh}} \mapsto ((\operatorname{\mathit{List}}.\operatorname{\mathit{count}}\left(j, \operatorname{\mathit{weights}}\left(l\right)\right): \int)), i\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Transfer.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The leading 31 by 31 block is the inherited transfer. Its outgoing entries to fresh states vanish. The remaining rows count occurrences in their checked successor lists.

**Definition 1.2 (Initial weights).**

$$\forall s: \operatorname{\mathit{State}}, (\operatorname{\mathit{initial}}\left(s\right) = (\operatorname{\mathit{if}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right) < 31 \operatorname{\mathit{then}} 0 \operatorname{\mathit{else}} 6))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Transfer.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

Six labelled first rows contribute to each fresh state, and none contribute to the inherited block.

**Definition 1.3 (Terminal weights).**

$$\forall s: \operatorname{\mathit{State}}, (\operatorname{\mathit{terminal}}\left(s\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{addCases}}\left(\operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{terminal}}, \lambda i: \operatorname{\mathit{Fresh}} \mapsto ((\operatorname{\mathit{if}} \operatorname{\mathit{budget}}\left(i\right) = 0 \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)), s\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Transfer.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The inherited terminal weights are preserved. A fresh state contributes exactly when its remaining budget is zero.

**Theorem 1.4 (Exact transitions for every valid boundary state).**

$$\forall p: \operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Nat}}, (\forall s: \operatorname{\mathit{State}}, ((\operatorname{\mathit{Valid}}\left(p, d\right)) \implies (\sum_{r: \operatorname{\mathit{Row}}} ((\operatorname{\mathit{if}} (\operatorname{\mathit{cost}}\left(p, r\right) \le d) \land (\operatorname{\mathit{cl}}\left(r, d - \operatorname{\mathit{cost}}\left(p, r\right)\right) = s) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{T}\left(\operatorname{\mathit{cl}}\left(p, d\right), s\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Transfer.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

In the inherited region the old weighted transitions apply. In the fresh region a common relabelling sends the source to its canonical representative and transports its full successor multiset.

**Theorem 1.5 (Exact terminal readout).**

$$\forall p: \operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Nat}}, ((\operatorname{\mathit{Valid}}\left(p, d\right)) \implies (\operatorname{\mathit{terminal}}\left(\operatorname{\mathit{cl}}\left(p, d\right)\right) = (\operatorname{\mathit{if}} d = 0 \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Transfer.terminal_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

Zero remaining budget accepts the array at either kind of state.

**Theorem 1.6 (Exact initial vector).**

$$\forall s: \operatorname{\mathit{State}}, (\sum_{r: \operatorname{\mathit{Row}}} ((\operatorname{\mathit{if}} (\operatorname{h}\left(r\right) \le 2) \land (\operatorname{\mathit{cl}}\left(r, 2 - \operatorname{h}\left(r\right)\right) = s) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{initial}}\left(s\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Transfer.initial_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The initial vector counts precisely the labelled choices for the first row in each class.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Transfer.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Transfer.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Transfer.initial_correct`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Transfer.terminal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Transfer.terminal_correct`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Transfer.transition_counts`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Laws](HardinA229635Laws.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635RowCertificate](HardinA229635RowCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Starts](HardinA229635Starts.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripClasses](../WidthSix/HardinA229532StripClasses.md)
