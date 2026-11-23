# The labeled exponential formula and the Mobius inverse

## Abstract

The labeled exponential formula and the Mobius inverse.

**Definition 1.1 (RootBlock).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.RootBlock`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.RootBlock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The subsets of the labeling set containing a specified root.

**Definition 1.2 (labeledWeight).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.labeledWeight`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.labeledWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Sum the product of block weights by size over the partitions with exactly k blocks.

**Theorem 1.3 (labeledWeight_root).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.labeledWeight_root`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.labeledWeight_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

When the root lies in the labeling set, obtain the weight for k plus one blocks by choosing its root block and partitioning the complement into k blocks.

**Definition 1.4 (blockSeries).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.blockSeries`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.blockSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The formal series with zero constant coefficient and degree-m coefficient given by w(m) divided by m factorial for positive m.

**Definition 1.5 (scale).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.scale`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.scale` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The image of n factorial divided by k factorial in the rational algebra.

**Theorem 1.6 (labeledWeight_coeff).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.labeledWeight_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.labeledWeight_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The weight of partitions of S into k blocks is the degree-card(S) coefficient of the k-th power of the block series, multiplied by card(S) factorial over k factorial.

**Definition 1.7 (assemblyKernel).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.assemblyKernel`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.assemblyKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The formal series with degree-k coefficient f(k) divided by k factorial.

**Theorem 1.8 (coeff_subst_blockSeries).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.coeff_subst_blockSeries`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.coeff_subst_blockSeries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

In degree n, substitution of the block series into H is the finite coefficient sum over powers from zero through n.

**Theorem 1.9 (labeled_subst).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.labeled_subst`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.labeled_subst` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Substituting the block series into the assembly series and multiplying the degree-card(S) coefficient by card(S) factorial gives the sum of products with f applied to the block count.

**Theorem 1.10 (assemblyKernel_one).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.assemblyKernel_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.assemblyKernel_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Constant block-count weight one gives the formal exponential.

**Definition 1.11 (oneBlockEGF).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.oneBlockEGF`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.oneBlockEGF` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The exponential generating function of the one-block sums of incidence Möbius values.

**Definition 1.12 (inverseCoefficient).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.inverseCoefficient`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.inverseCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The degree-k inverse-series numerator is the binomial coefficient choosing k minus one from k plus r minus two.

**Definition 1.13 (inverseEGF).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.inverseEGF`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.inverseEGF` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The exponential generating function of the one-block extension coefficients, with zero constant term.

**Theorem 1.14 (inverseEGF_subst_oneBlockEGF).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.inverseEGF_subst_oneBlockEGF`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.inverseEGF_subst_oneBlockEGF` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

For positive r, substituting the one-block Möbius series into the extension-count series gives X.

**Definition 1.15 (markedBlockEGF).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.markedBlockEGF`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.markedBlockEGF` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The one-block exponential generating function with a size-m block marked by X to the power m minus one in the polynomial coefficient ring.

**Theorem 1.16 (psiComplete_exponential).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.psiComplete_exponential`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.psiComplete_exponential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

For every n and r, the rank polynomial is n factorial times the degree-n coefficient of the exponential composed with the marked block series.

**Definition 1.17 (inverseFactor).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.inverseFactor`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.inverseFactor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The finite series whose coefficient in degree i at most q is the binomial coefficient choosing i from q divided by (i+1) factorial, and zero beyond q.

**Theorem 1.18 (inverseEGF_factor).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.inverseEGF_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.inverseEGF_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

For r equal to q plus two, the inverse series is the product of the formal variable, its exponential, and the finite factor indexed by q.

## References

- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.RootBlock`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.assemblyKernel`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.assemblyKernel_one`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.blockSeries`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.coeff_subst_blockSeries`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.inverseCoefficient`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.inverseEGF`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.inverseEGF_factor`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.inverseEGF_subst_oneBlockEGF`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.inverseFactor`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.labeledWeight`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.labeledWeight_coeff`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.labeledWeight_root`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.labeled_subst`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.markedBlockEGF`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.oneBlockEGF`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.psiComplete_exponential`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.scale`
- Dependency: [D5/S3/Combinatorics/WeightedBond/PartitionExpansion](PartitionExpansion.md)
