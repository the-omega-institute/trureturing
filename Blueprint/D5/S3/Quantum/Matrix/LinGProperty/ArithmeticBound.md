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

**Theorem 1.2 (Trace ceiling for a positive matrix).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.trace_identity_sub_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.trace_identity_sub_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every finite index type with decidable equality and every positive semidefinite complex square matrix A, Re(tr A) I minus A is positive semidefinite. The spectral theorem bounds each nonnegative eigenvalue by their sum.

**Theorem 1.3 (Row Gram comparison).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.row_gram_sum_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.row_gram_sum_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For finite row and column index types with decidable equality and arbitrary complex matrices U,V of the same rectangular shape, 2(U U-adjoint+V V-adjoint) minus (U+V)(U+V)-adjoint is positive semidefinite. Expanding identifies this matrix with (U-V)(U-V)-adjoint.

**Theorem 1.4 (Ordered spectra from the characteristic polynomial).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.eigenvalues_zero_eq_of_charpoly`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.eigenvalues_zero_eq_of_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For Hermitian complex matrices A,B on the same finite index type with decidable equality, equality of their characteristic polynomials implies equality of every decreasingly ordered eigenvalue. The index ranges over Fin(cardinality of the index type).

**Theorem 1.5 (The leading rectangular Gram spectrum).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.rectangular_gram_eigenvalues`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.rectangular_gram_eigenvalues` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every natural n, every complex matrix T with n rows and 2n columns indexed by Fin n plus Fin n, and every j in Fin n, the j-th decreasing eigenvalue of T-adjoint T equals the j-th decreasing eigenvalue of T T-adjoint. The assertion includes zero eigenvalues and imposes no rank condition.

**Theorem 1.6 (Ordered eigenvalues respect positive differences).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.eigenvalues_zero_mono_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.eigenvalues_zero_mono_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For Hermitian complex matrices A,B on any finite index type with decidable equality, positivity of B-A implies lambda_j(A)<=lambda_j(B) at every decreasingly ordered index. Reindexing transports the established finite-dimensional comparison.

**Theorem 1.7 (Nonnegative scalar scaling of the ordered spectrum).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.eigenvalues_zero_smul_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.eigenvalues_zero_smul_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For a Hermitian complex matrix A on any finite index type with decidable equality, a nonnegative real r and a Hermitian witness for rA, every decreasingly ordered eigenvalue satisfies lambda_j(rA)=r lambda_j(A). Zero scaling and empty index types are included.

**Theorem 1.8 (Scalar translation of the ordered spectrum).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.eigenvalues_zero_add_scalar_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.eigenvalues_zero_add_scalar_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For a Hermitian complex matrix A on any finite index type with decidable equality, any real r and a Hermitian witness for A+rI, every decreasingly ordered eigenvalue satisfies lambda_j(A+rI)=lambda_j(A)+r.

**Theorem 1.9 (The leading Hermitian dilation spectrum).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.dilation_eigenvalues`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.dilation_eigenvalues` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every natural n, every complex n by n matrix X and a Hermitian witness for the block matrix [0 X; X-adjoint 0], its first n decreasingly ordered eigenvalues are the decreasingly ordered singular values of X. A singular value decomposition and zero-aware ordering identify the entire leading spectrum.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.dilation_eigenvalues`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.eigenvalues_zero_add_scalar_finite`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.eigenvalues_zero_eq_of_charpoly`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.eigenvalues_zero_mono_finite`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.eigenvalues_zero_smul_finite`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.normalized_arithmetic_bound`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.rectangular_gram_eigenvalues`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.row_gram_sum_comparison`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.trace_identity_sub_posSemidef`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/PhaseRotation](PhaseRotation.md)
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/ScalarPerturbation](ScalarPerturbation.md)
- Dependency: [D5/S3/Quantum/Schatten/SingularValueOrder](../../Schatten/SingularValueOrder.md)
