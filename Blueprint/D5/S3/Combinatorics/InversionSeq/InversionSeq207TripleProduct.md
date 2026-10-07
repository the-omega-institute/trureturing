# Formal Jacobi Triple Product

## Abstract

Euler convolution and Durfee normalization give a formal Jacobi triple product.

**Definition 1.1 (Shifted Euler factor).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq207TripleProduct.shiftedEulerFactor`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/InversionSeq207TripleProduct.shiftedEulerFactor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

The shifted Euler factor is the Laurent-valued power series whose coefficient at each degree sums the Euler coefficients after multiplication by the corresponding power of the series variable.

**Definition 1.2 (Formal theta series).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq207TripleProduct.formalTheta`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/InversionSeq207TripleProduct.formalTheta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

The formal theta series is the product of the Euler Laurent expansion and the inverted shifted Euler factor.

**Theorem 1.3 (Formal triple product identity).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq207TripleProduct.formal_triple_product`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq207TripleProduct.formal_triple_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For every integer index, the pentagonal power series multiplied by the power series of the index coefficient of formal theta equals the signed monomial at the triangular exponent determined by the sign of the index.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq207TripleProduct.formalTheta`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq207TripleProduct.formal_triple_product`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq207TripleProduct.shiftedEulerFactor`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq207Durfee](InversionSeq207Durfee.md)
