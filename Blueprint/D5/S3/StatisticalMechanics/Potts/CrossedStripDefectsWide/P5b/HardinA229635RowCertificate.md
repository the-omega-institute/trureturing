# Verified fresh transition lists

## Abstract

All fresh source states are checked against the literal successor lists.

**Theorem 1.1 (Exact outgoing lists for all fresh states).**

$$\forall i: \operatorname{\mathit{Fresh}}, (\operatorname{\mathit{outgoing}}\left(\operatorname{\mathit{rep}}\left(i\right), \operatorname{\mathit{budget}}\left(i\right)\right) = \operatorname{\mathit{weights}}\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635RowCertificate.checked_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The weighted outgoing lists enumerate all labelled successor rows at the representative and remaining budget. Repetition records multiplicity.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635RowCertificate.checked_weights`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows0](HardinA229635Rows0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows1](HardinA229635Rows1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows2](HardinA229635Rows2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows3](HardinA229635Rows3.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows4](HardinA229635Rows4.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows5](HardinA229635Rows5.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows6](HardinA229635Rows6.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows7](HardinA229635Rows7.md)
