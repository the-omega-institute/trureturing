# Forward vectors

## Abstract

The stored integer row vectors are indexed by the number of transfer steps.

**Definition 1.1 (Cached forward vector entries).**

$$\forall i: \operatorname{\mathit{Fin}}\left(31\right), (\forall s: \operatorname{\mathit{State}}, (\operatorname{\mathit{power}}\left(i, s\right) = \operatorname{\mathit{Vector}}.\operatorname{\mathit{get}}\left(\operatorname{\mathit{Vector}}.\operatorname{\mathit{get}}\left(\operatorname{\mathit{powerTable}}, i\right), s\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Powers.power` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The table stores integer row vectors at powers zero through thirty. Each vector has one entry for each of the 127 transfer states.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Powers.power`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseData](HardinA229635SparseData.md)
