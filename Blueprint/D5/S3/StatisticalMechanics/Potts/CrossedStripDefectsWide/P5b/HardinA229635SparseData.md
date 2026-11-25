# Sparse transfer data

## Abstract

Successor multiplicities and the corresponding incoming lists.

**Definition 1.1 (Outgoing classes by source).**

$$\forall s: \operatorname{\mathit{State}}, (\operatorname{\mathit{outgoingClasses}}\left(s\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{addCases}}\left(\operatorname{\mathit{Vector}}.\operatorname{\mathit{get}}\left(\operatorname{\mathit{oldRows}}\right), \operatorname{\mathit{weights}}, s\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseData.outgoingClasses` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The first 31 rows use the inherited block. The remaining 96 rows list the checked fresh classes.

**Definition 1.2 (Incoming classes by destination).**

$$\forall j: \operatorname{\mathit{State}}, (\operatorname{\mathit{incomingClasses}}\left(j\right) = \operatorname{\mathit{Vector}}.\operatorname{\mathit{get}}\left(\operatorname{\mathit{incomingRows}}, j\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseData.incomingClasses` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

For each destination, the table stores the sources of incoming transitions in increasing source order, with multiplicity.

**Definition 1.3 (Transposing the outgoing lists).**

$$\forall j: \operatorname{\mathit{State}}, (\operatorname{\mathit{transposeLists}}\left(j\right) = \operatorname{\mathit{List}}.\operatorname{\mathit{flatten}}\left(\operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{State}} \mapsto (\operatorname{\mathit{List}}.\operatorname{\mathit{replicate}}\left(\operatorname{\mathit{List}}.\operatorname{\mathit{count}}\left(j, \operatorname{\mathit{outgoingClasses}}\left(i\right)\right), i\right))\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseData.transposeLists` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

Each lossless transpose entry includes the source once for every occurrence of the destination in that source's list.

**Definition 1.4 (Sparse update by incoming classes).**

$$\forall v: (\operatorname{\mathit{State}}) \to (\operatorname{\mathit{Int}}), (\forall j: \operatorname{\mathit{State}}, (\operatorname{\mathit{step}}\left(v, j\right) = \operatorname{\mathit{List}}.\operatorname{\mathit{sum}}\left(\operatorname{\mathit{List}}.\operatorname{\mathit{map}}\left(v, \operatorname{\mathit{incomingClasses}}\left(j\right)\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseData.step` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

Each repeated incoming source contributes its current weight one more time.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseData.incomingClasses`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseData.outgoingClasses`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseData.step`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseData.transposeLists`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows](HardinA229635Rows.md)
