# Unitarily invariant norms and symmetric diagonal gauges

## Abstract

Unitarily invariant norms and symmetric diagonal gauges.

**Definition 1.1 (Unitarily invariant complex matrix norms).**

Lean statement: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.UINorm`

*Formalization.* `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.UINorm` (`✓ std3`).

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

For each natural n, UINorm consists of a real-valued function N on complex n by n matrices that is nonnegative, vanishes exactly at zero, is subadditive, satisfies N(cX)=|c|N(X) for every complex scalar c, and satisfies N(UXV)=N(X) for unitary U and V.

**Theorem 1.2 (Symmetric gauge representation).**

Lean statement: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_eq_singularValues`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_eq_singularValues` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

For every complex square matrix X, N(X)=N(diag(s(X))), where s(X) is its nonnegative singular-value vector. Thus the real diagonal gauge γ(x)=N(diag(x)) represents N as γ(s(X)); no ordering of the singular values is required.

**Theorem 1.3 (Adjoint invariance).**

Lean statement: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_conjTranspose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_conjTranspose` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

For every complex square matrix X, N(X*)=N(X). Singular-value decomposition exchanges the two unitary factors and preserves the nonnegative diagonal.

**Theorem 1.4 (Transpose invariance).**

Lean statement: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_transpose` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

For every complex square matrix X, N(Xᵀ)=N(X), including matrices with nonreal entries. Transposing a singular-value decomposition preserves its diagonal and gives unitary factors.

**Theorem 1.5 (Coordinate contractions).**

Lean statement: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_diagonal_contract`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_diagonal_contract` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

For real vectors x and c with |cᵢ|≤1 at every coordinate, N(diag(cᵢxᵢ))≤N(diag(x)). A convex combination with a diagonal sign reflection contracts one coordinate, and iteration contracts them all.

**Theorem 1.6 (Absolute coordinate domination).**

Lean statement: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_diagonal_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_diagonal_mono` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

For real vectors x and y satisfying |xᵢ|≤|yᵢ| at every coordinate, N(diag(x))≤N(diag(y)). Zero coordinates are permitted.

**Theorem 1.7 (Permutation invariance of the gauge).**

Lean statement: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_diagonal_perm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_diagonal_perm` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

For every real vector x and every permutation σ, N(diag(x∘σ))=N(diag(x)). Permutation conjugation preserves the norm.

**Theorem 1.8 (The gauge of a permutation matching).**

Lean statement: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_diagonal_permMatrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_diagonal_permMatrix` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

For real diagonal weights a and b and a permutation matrix Pσ whose row i has its nonzero entry at column σ(i), N(diag(a)Pσdiag(b))=N(diag(aᵢbσ(i))). No sign assumption on the weights is needed.

**Theorem 1.9 (Fan dominance for diagonal gauges).**

Lean statement: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_diagonal_weakMajorization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_diagonal_weakMajorization` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

Let z and q be nonnegative real vectors, with z decreasing. If every initial sum of z is at most the corresponding initial sum of q, then N(diag(z))≤N(diag(q)). In particular, weak majorization of decreasing nonnegative vectors implies the norm inequality; the stated hypothesis does not require q to be decreasing.

## References

- Truth anchor: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_conjTranspose`
- Truth anchor: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_diagonal_contract`
- Truth anchor: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_diagonal_mono`
- Truth anchor: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_diagonal_perm`
- Truth anchor: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_diagonal_permMatrix`
- Truth anchor: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_diagonal_weakMajorization`
- Truth anchor: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_eq_singularValues`
- Truth anchor: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N_transpose`
- Truth anchor: `D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.UINorm`
- Dependency: [D5/S3/Geometry/AlphaGeometry/MajorizationTransfer](../../Geometry/AlphaGeometry/MajorizationTransfer.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Schatten/CompoundMatrices](CompoundMatrices.md)
