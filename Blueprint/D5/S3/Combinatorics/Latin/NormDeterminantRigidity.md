# Norm–determinant rigidity of unitary products

## Abstract

Complex n-by-n factors of squared Frobenius norm n with a unitary product are unitary.

**Theorem 1.1 (Determinant bound and its equality case).**

Lean statement: `D5/S3/Combinatorics/Latin/NormDeterminantRigidity.norm_det_le_one_and_rigid`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/NormDeterminantRigidity.norm_det_le_one_and_rigid` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Resolving Pozsgay–Wanless's factor-perfection question and qubit decomposition conjecture*. DOI: [10.5281/zenodo.23903313](https://doi.org/10.5281/zenodo.23903313). URL: <https://zenodo.org/records/23903313>.

*Commentary.*

Let M be a complex n×n matrix whose squared Frobenius norm ∑ᵢ∑ⱼ‖M(i,j)‖² equals n. Then ‖det M‖ ≤ 1, and ‖det M‖ = 1 implies that M is unitary. The Hermitian matrix MᴴM is positive semidefinite with eigenvalues λ₁,…,λₙ ≥ 0; its trace gives ∑λᵢ = n and its determinant gives ∏λᵢ = ‖det M‖². From λ ≤ exp(λ−1) one gets ∏λᵢ ≤ exp(∑(λᵢ−1)) = 1. If ‖det M‖ = 1, every λᵢ is positive, and a λⱼ ≠ 1 would make the inequality strict, so every eigenvalue is 1 and the spectral theorem gives MᴴM = 1.

**Theorem 1.2 (Factors of a unitary product).**

Lean statement: `D5/S3/Combinatorics/Latin/NormDeterminantRigidity.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/NormDeterminantRigidity.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Resolving Pozsgay–Wanless's factor-perfection question and qubit decomposition conjecture*. DOI: [10.5281/zenodo.23903313](https://doi.org/10.5281/zenodo.23903313). URL: <https://zenodo.org/records/23903313>.

*Commentary.*

For every size n, including n = 0, and every finite list of complex n×n matrices, each of squared Frobenius norm n, if the product of the list is unitary then every matrix in the list is unitary. The determinant norm of a unitary matrix is 1 and determinant norms are multiplicative; since each factor has determinant norm at most 1, a product of these norms equal to 1 forces each of them to be 1, and the equality case above applies to every factor.

## References

- Truth anchor: `D5/S3/Combinatorics/Latin/NormDeterminantRigidity.norm_det_le_one_and_rigid`
- Truth anchor: `D5/S3/Combinatorics/Latin/NormDeterminantRigidity.result`
