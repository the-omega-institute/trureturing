# First-row census

## Abstract

Initial state multiplicities for labelled first rows.

**Definition 1.1 (Stored first-row class list).**

$$\operatorname{\mathit{startTable}}: \operatorname{\mathit{List}}\left(\operatorname{\mathit{State}}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Starts.startTable` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The definition stores an explicit list of state indices. The equality below relates it to the enumeration of labelled first rows.

**Theorem 1.2 (Exact first-row list).**

$$\operatorname{\mathit{startClasses}} = \operatorname{\mathit{startTable}}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Starts.checked_starts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

Enumerating all labelled first rows gives the stored list.

**Theorem 1.3 (First-row multiplicity in each class).**

$$\forall s: \operatorname{\mathit{State}}, ((\operatorname{\mathit{List}}.\operatorname{\mathit{count}}\left(s, \operatorname{\mathit{startTable}}\right): \int) = (\operatorname{\mathit{if}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right) < 31 \operatorname{\mathit{then}} 0 \operatorname{\mathit{else}} 6))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Starts.start_tallies` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

Paying for the first row starts in the fresh sector. Each fresh state occurs six times.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Starts.checked_starts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Starts.startTable`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Starts.start_tallies`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State](HardinA229635State.md)
