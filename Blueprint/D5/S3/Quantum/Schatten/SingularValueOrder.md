# Gram order and decreasing singular values

## Abstract

Gram order and decreasing singular values.

**Theorem 1.1 (Hermitian eigenvalue order).**

Lean statement: `D5/S3/Quantum/Schatten/SingularValueOrder.eigenvalues_zero_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/SingularValueOrder.eigenvalues_zero_mono` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

For every dimension, Hermitian complex matrices H,K with K−H positive semidefinite satisfy λᵢ(H)≤λᵢ(K) at every decreasing eigenvalue index. The spectral subspace comparison includes repeated eigenvalues.

**Theorem 1.2 (Nonnegative eigenvalue scaling).**

Lean statement: `D5/S3/Quantum/Schatten/SingularValueOrder.eigenvalues_zero_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/SingularValueOrder.eigenvalues_zero_smul` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

For every dimension, Hermitian complex matrix H and nonnegative real q, the decreasing eigenvalues satisfy λᵢ(qH)=qλᵢ(H) at every index. The formula includes q=0.

**Theorem 1.3 (Singular values from Gram eigenvalues).**

Lean statement: `D5/S3/Quantum/Schatten/SingularValueOrder.singularValuesSorted_eq_sqrt_eigenvalues_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/SingularValueOrder.singularValuesSorted_eq_sqrt_eigenvalues_zero` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

For each index i, the ith decreasing singular value of a complex square matrix A is the nonnegative square root of the ith decreasing eigenvalue of A*A. Eigenvalues are counted with multiplicity.

**Theorem 1.4 (Courant–Fischer monotonicity).**

Lean statement: `D5/S3/Quantum/Schatten/SingularValueOrder.gram_singularValuesSorted_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/SingularValueOrder.gram_singularValuesSorted_mono` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

If B*B−A*A is positive semidefinite, then sᵢ(A)≤sᵢ(B) for every decreasing singular-value index i. Courant–Fischer comparison of the two Hermitian Gram matrices gives the eigenvalue inequality before taking square roots.

**Theorem 1.5 (Unitary left multiplication).**

Lean statement: `D5/S3/Quantum/Schatten/SingularValueOrder.singularValuesSorted_unitary_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/SingularValueOrder.singularValuesSorted_unitary_mul` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

For every unitary U and every complex square A, sᵢ(UA)=sᵢ(A) at every decreasing singular-value index.

**Theorem 1.6 (Adjoint singular values).**

Lean statement: `D5/S3/Quantum/Schatten/SingularValueOrder.singularValuesSorted_conjTranspose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/SingularValueOrder.singularValuesSorted_conjTranspose` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

For every complex square A, sᵢ(A*)=sᵢ(A) at every decreasing singular-value index, including zero singular values.

**Theorem 1.7 (Nonnegative scalar homogeneity).**

Lean statement: `D5/S3/Quantum/Schatten/SingularValueOrder.singularValuesSorted_smul_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/SingularValueOrder.singularValuesSorted_smul_nonneg` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

For every nonnegative real r and complex square A, sᵢ(rA)=r sᵢ(A) at every decreasing singular-value index. The formula includes r=0.

## References

- Truth anchor: `D5/S3/Quantum/Schatten/SingularValueOrder.eigenvalues_zero_mono`
- Truth anchor: `D5/S3/Quantum/Schatten/SingularValueOrder.eigenvalues_zero_smul`
- Truth anchor: `D5/S3/Quantum/Schatten/SingularValueOrder.gram_singularValuesSorted_mono`
- Truth anchor: `D5/S3/Quantum/Schatten/SingularValueOrder.singularValuesSorted_conjTranspose`
- Truth anchor: `D5/S3/Quantum/Schatten/SingularValueOrder.singularValuesSorted_eq_sqrt_eigenvalues_zero`
- Truth anchor: `D5/S3/Quantum/Schatten/SingularValueOrder.singularValuesSorted_smul_nonneg`
- Truth anchor: `D5/S3/Quantum/Schatten/SingularValueOrder.singularValuesSorted_unitary_mul`
- Dependency: [D5/S3/Quantum/Schatten/CompoundMatrices](CompoundMatrices.md)
- Dependency: [D5/S3/SpectralTopology/HermitianEigenvaluePerturbation](../../SpectralTopology/HermitianEigenvaluePerturbation.md)
