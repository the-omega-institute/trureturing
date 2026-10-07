# Formal Euler Expansion

## Abstract

Finite Euler factors define a unique normalized coefficient series and its Laurent expansion.

**Definition 1.1 (Euler denominator).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq207Euler.eulerDenominator`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/InversionSeq207Euler.eulerDenominator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For a natural number index, eulerDenominator is the finite product of 1 minus the power-series variable raised to each positive exponent below index.

**Definition 1.2 (Euler coefficient series).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq207Euler.eulerCoefficients`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/InversionSeq207Euler.eulerCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For a natural number index, eulerCoefficients is the signed monomial at the triangular exponent multiplied by the inverse of eulerDenominator with constant coefficient one.

**Definition 1.3 (Laurent expansion).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq207Euler.eulerLaurentExpansion`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/InversionSeq207Euler.eulerLaurentExpansion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

The Laurent expansion is the power series whose coefficient at each degree is the finite sum of Euler coefficients paired with Laurent monomials indexed by natural numbers.

**Theorem 1.4 (Euler coefficient construction).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq207Euler.euler_coefficient_construction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq207Euler.euler_coefficient_construction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

The Euler coefficient series has constant coefficient one and satisfies the rescaling equation series equals (1 minus q) times its q-rescaling. It is the unique series with these properties. Its coefficients vanish below the triangular support, admit the finite polynomial coefficient description, and sum as a Laurent power series to eulerLaurentExpansion.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq207Euler.eulerCoefficients`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq207Euler.eulerDenominator`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq207Euler.eulerLaurentExpansion`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq207Euler.euler_coefficient_construction`
- Dependency: [D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiHeine](../TwoColorPartition/AndrewsElBachraouiHeine.md)
