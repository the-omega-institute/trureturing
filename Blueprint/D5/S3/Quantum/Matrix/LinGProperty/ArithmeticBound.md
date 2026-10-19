# The trace-corrected arithmetic bound

## Abstract

The arithmetic spectral bound retains the deficit in the normalized block overlap.

**Theorem 1.1 (An indexed arithmetic bound with trace deficit).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.normalized_arithmetic_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.normalized_arithmetic_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

Let [A X; X-adjoint B] be positive semidefinite, with tr A=tr B=1. Every decreasingly ordered singular value satisfies 2 s_j(X) <= lambda_j(A+B)+1-|tr X|. All finite dimensions and singular blocks are included.

A unit phase makes the trace of X real and nonnegative without changing block positivity or any singular value. The Hermitian dilation [0 X; X-adjoint 0] has leading eigenvalues s_j(X). An explicit similarity from a singular value decomposition proves this identity, while Loewner monotonicity compares twice this dilation with the original positive block matrix.

Write the positive block matrix as Z Z-adjoint and partition its rows into U and V. Its eigenvalues agree with those of U-adjoint U+V-adjoint V. The latter matrix is one half of the sum Gram plus one half of the difference Gram. A positive matrix is bounded above by its trace times the identity, so the difference Gram contributes exactly 1-Re tr X.

The leading eigenvalues of rectangular row and column Grams agree after zero padding. Finally, the row sum Gram (U+V)(U+V)-adjoint is bounded above by 2(A+B). Combining these comparisons gives the indexed inequality.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.normalized_arithmetic_bound`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/PhaseRotation](PhaseRotation.md)
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/ScalarPerturbation](ScalarPerturbation.md)
- Dependency: [D5/S3/Quantum/Schatten/SingularValueOrder](../../Schatten/SingularValueOrder.md)
