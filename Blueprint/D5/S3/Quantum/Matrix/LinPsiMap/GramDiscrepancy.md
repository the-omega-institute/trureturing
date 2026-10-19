# The Gram-discrepancy spectral estimate

## Abstract

A Loewner bound on Gram discrepancy yields an indexed singular-value estimate.

**Theorem 1.1 (An indexed spectral estimate from discrepancy).**

Lean statement: `D5/S3/Quantum/Matrix/LinPsiMap/GramDiscrepancy.gram_discrepancy_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinPsiMap/GramDiscrepancy.gram_discrepancy_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *New properties for certain positive semidefinite matrices*. DOI: [10.48550/arXiv.1609.08231](https://doi.org/10.48550/arXiv.1609.08231). URL: <https://arxiv.org/abs/1609.08231v1>.

*Commentary.*

For a positive semidefinite block matrix [P Y; Y-adjoint Q], assume P+Q−Y−Y-adjoint is at most delta I in Loewner order, with delta nonnegative. Then every decreasing singular value satisfies 2 s_j(Y) <= lambda_j(P+Q)+delta/2. The statement includes singular matrices and repeated eigenvalues.

In a Gram factorization, write the row blocks as U and V and put F=U+V and E=U−V. The discrepancy is E E-adjoint. Its scalar identity bound also bounds E-adjoint E. The full column Gram is one half F-adjoint F plus one half E-adjoint E, while F F-adjoint is at most twice P+Q.

The existing row-column Gram spectral correspondence and eigenvalue monotonicity bound the leading eigenvalues of the original block. Its signed off-diagonal dilation is bounded by that positive block and has leading eigenvalues twice the singular values of Y. Combining the comparisons gives the stated estimate.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/LinPsiMap/GramDiscrepancy.gram_discrepancy_bound`
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound](../LinGProperty/ArithmeticBound.md)
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound](../LinGProperty/GeometricMeanBound.md)
