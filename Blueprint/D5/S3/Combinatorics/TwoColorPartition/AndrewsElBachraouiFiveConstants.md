# D-prime leading constants and the Wallis gap

## Abstract

D-prime leading constants and the Wallis gap.

**Definition 1.1 (Odd denominator product).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.oddProd`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.oddProd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

The real product of 2i plus one for natural i strictly below h.

**Definition 1.2 (Even numerator product).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.evenProd`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.evenProd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

The real product of 2i plus two for natural i strictly below h.

**Definition 1.3 (Rational coefficient leading constant).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.rationalConstant`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.rationalConstant` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

The product of the fractions 2i plus two over 2i plus three, for i below h minus one, divided by h factorial times oddProd h.

**Definition 1.4 (Gauss upper leading constant).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.productConstant`

*Formalization.* `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.productConstant` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

The value pi divided by two raised to h plus one times the square of h factorial.

**Theorem 1.5 (Alternating subset constant).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.subset_constant`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.subset_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For every finite set s, the sum over its subsets S of minus one raised to the cardinality of S divided by twice that cardinality plus one equals the product, for i below the cardinality of s, of 2i plus two over 2i plus three. Integrating the finite subset expansion of one minus x squared and using the existing sine-power integral proves the formula.

**Theorem 1.6 (Strict Wallis leading gap).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.leading_gap_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.leading_gap_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For every natural h at least one, rationalConstant h minus productConstant h is strictly positive. The existing Wallis lower bound gives a strict inequality between the squared even-to-odd product ratio and pi times h.

## References

- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.evenProd`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.leading_gap_pos`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.oddProd`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.productConstant`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.rationalConstant`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.subset_constant`
