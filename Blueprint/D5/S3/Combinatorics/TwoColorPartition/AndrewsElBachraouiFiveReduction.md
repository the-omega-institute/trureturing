# Exact D-prime source coefficient transformations

## Abstract

Exact D-prime source coefficient transformations.

**Definition 1.1 (Finite rational truncation).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.rationalTrunc`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.rationalTrunc` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For k, m and N natural, this is the finite transformed numerator sum through N, multiplied by the first k minus one odd geometric denominators.

**Definition 1.2 (Finite subtracted product).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.productTrunc`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.productTrunc` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

The product has the source factors with exponents 2 plus 2i and 2k plus 2i and two odd geometric denominator factors, for i from zero through N.

**Theorem 1.3 (Geometric inverse identity).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.geom_mul_one_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.geom_mul_one_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For every positive natural e, geom e times one minus X raised to e equals one. The series is the original integer coefficient definition.

**Definition 1.4 (Finite offset indices).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.offsetIndices`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.offsetIndices` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

The disjoint sum of ranges m minus one and k minus m minus one indexes the even and odd source numerator offsets. Empty endpoint ranges are retained.

**Definition 1.5 (Source numerator offsets).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.offset`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.offset` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

An even index i has offset 2 plus 2i. An odd index i has offset 2m plus one plus 2i.

**Definition 1.6 (Fixed rational series).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.rationalSeries`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.rationalSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

The sum over subsets of the offset indices has sign minus one raised to the subset cardinality, monomial degree equal to the sum of its offsets, and geometric step twice its cardinality plus one. The sum is multiplied by the odd geometric denominator product.

**Theorem 1.7 (Exact transformed source coefficient).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.source_coefficient_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.source_coefficient_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For every k, m and n with one at most m and m less than k, the original dCoeff k m n equals the coefficient of degree n of rationalTrunc k m n minus productTrunc k n. There is no degree shift. Two applications of the existing nilpotent q-binomial identity prove the transformation in the quotient by X raised to n plus one.

**Definition 1.8 (Consistent Gauss coefficients).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.gaussSeries`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.gaussSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

This fixed integer power series has coefficient at n equal to the source productTrunc 2 n coefficient. Truncation stability connects its lower coefficients to each finite product.

**Definition 1.9 (Finite even convolution product).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.productSeries`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.productSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For k at least two this is gaussSeries multiplied by geom 4 through geom of twice k minus two.

**Theorem 1.10 (Fixed-series source coefficient identity).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.source_coefficient_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.source_coefficient_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For every k, m and n with one at most m and m less than k, dCoeff k m n is the degree n coefficient of rationalSeries k m minus that of productSeries k. Finite subset expansion, geometric summation and product cancellation prove every coefficient bridge.

## References

- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.gaussSeries`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.geom_mul_one_sub`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.offset`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.offsetIndices`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.productSeries`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.productTrunc`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.rationalSeries`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.rationalTrunc`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.source_coefficient_expansion`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.source_coefficient_reduction`
- Dependency: [D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiBounds](AndrewsElBachraouiBounds.md)
- Dependency: [D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiHeine](AndrewsElBachraouiHeine.md)
