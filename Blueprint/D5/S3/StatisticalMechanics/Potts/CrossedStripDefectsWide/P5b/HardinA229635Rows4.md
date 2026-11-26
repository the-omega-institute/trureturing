# Successor lists for fresh states 48 through 59

## Abstract

Each list comes from checking every labelled candidate successor against the remaining budget.

**Theorem 1.1 (Successor lists for fresh states 48 through 59).**

$$\forall j: \operatorname{\mathit{Fin}}\left(12\right), (\operatorname{\mathit{let}} i: \operatorname{\mathit{Fresh}} := 48 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right); (\operatorname{\mathit{outgoing}}\left(\operatorname{\mathit{rep}}\left(i\right), \operatorname{\mathit{budget}}\left(i\right)\right) = \operatorname{\mathit{weights}}\left(i\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows4.checked` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

Each list comes from checking every labelled candidate successor against the remaining budget.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows4.checked`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Sample](HardinA229635Sample.md)
