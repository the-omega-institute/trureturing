# The literal count

## Abstract

A six-to-one relation between labelled and canonical arrays.

**Theorem 1.1 (Six labelled arrays per canonical array).**

$$\forall m: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{literalCount}}\left(3, \operatorname{\mathit{horizontal}}, \operatorname{\mathit{between}}, 2, m + 1\right) = 6 \cdot \operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(m + 1, 6\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Literal.six_labellings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The two literal bond sets agree with the transfer bond sets. A constant array already has more than two horizontal bonds in one row. A nonconstant array has six distinct relabellings, including when only two colours are used.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Literal.six_labellings`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripData](../WidthSix/HardinA229532StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn](../../StripDefects/HardinA229637RowColumn.md)
