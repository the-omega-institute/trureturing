# Wasserstein power means and eigenvalue products

## Abstract

The geometric and Wasserstein matrix means, their real power transform, and weak log-majorization through decreasingly sorted eigenvalue products.

arXiv:2301.07934v4, §5, Conjecture 5.7.

A ⋄t B := (1 − t)² A + t² B + t(1 − t)[A(A^{−1} #B) + (A^{−1} #B)A]

Conjecture 5.7. Let A, B ∈ Pm and t ∈ (0, 1). Then (A^p ⋄t B^p)^{1/p} ց≺w log exp((1 − t) log A + t log B) as p ց 0.

**Definition 1.1 (The weighted Wasserstein mean).**

Lean statement: `D5/S3/Quantum/Matrix/WassersteinMean.wassersteinMean`

*Formalization.* `D5/S3/Quantum/Matrix/WassersteinMean.wassersteinMean` (`✓ std3`).

*Citation.* Luyining Gan; Sejong Kim (2024). *Weak log-majorization between the geometric and Wasserstein means*. DOI: [10.48550/arXiv.2301.07934](https://doi.org/10.48550/arXiv.2301.07934). URL: <https://arxiv.org/abs/2301.07934>.

*Commentary.*

The mean is exactly the displayed polynomial expression in A, B and A⁻¹ # B, with real weight t. The geometric mean reuses the base-first weighted mean in PsiMeanTraceConcavity at weight 1/2, using CFC.rpow. For positive definite inputs and 0≤t≤1 it also equals ((1−t)I+tT) A ((1−t)I+tT), where T=A⁻¹ # B is the positive definite solution of TAT=B.

**Definition 1.2 (The power-transformed Wasserstein mean).**

Lean statement: `D5/S3/Quantum/Matrix/WassersteinMean.powerMean`

*Formalization.* `D5/S3/Quantum/Matrix/WassersteinMean.powerMean` (`✓ std3`).

*Citation.* Luyining Gan; Sejong Kim (2024). *Weak log-majorization between the geometric and Wasserstein means*. DOI: [10.48550/arXiv.2301.07934](https://doi.org/10.48550/arXiv.2301.07934). URL: <https://arxiv.org/abs/2301.07934>.

*Commentary.*

F A B t p is (A^p ⋄t B^p)^(1/p), with both the input powers and the outer reciprocal power interpreted by the real continuous functional calculus via SpectralPower.mpow. The proposed limit uses that module’s LE t A B, namely exp((1−t) log A+t log B). This is the expression in Conjecture 5.7.

**Definition 1.3 (Weak log-majorization).**

Lean statement: `D5/S3/Quantum/Matrix/WassersteinMean.weakLogMajorization`

*Formalization.* `D5/S3/Quantum/Matrix/WassersteinMean.weakLogMajorization` (`✓ std3`).

*Citation.* Luyining Gan; Sejong Kim (2024). *Weak log-majorization between the geometric and Wasserstein means*. DOI: [10.48550/arXiv.2301.07934](https://doi.org/10.48550/arXiv.2301.07934). URL: <https://arxiv.org/abs/2301.07934>.

*Commentary.*

Hermitian witnesses supply real eigenvalues sorted in decreasing order. For each prefix length k up to the dimension, the product of the first k eigenvalues of X is at most the corresponding product for Y. The empty prefix is harmless; the full prefix is essential. For the positive definite matrices in the conjecture, all eigenvalues are positive.

**Theorem 1.4 (The full prefix compares determinants).**

Lean statement: `D5/S3/Quantum/Matrix/WassersteinMean.weakLogMajorization_det_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/WassersteinMean.weakLogMajorization_det_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luyining Gan; Sejong Kim (2024). *Weak log-majorization between the geometric and Wasserstein means*. DOI: [10.48550/arXiv.2301.07934](https://doi.org/10.48550/arXiv.2301.07934). URL: <https://arxiv.org/abs/2301.07934>.

*Commentary.*

The prefix containing every eigenvalue gives det X≤det Y for the real determinants of Hermitian matrices. The determinant equals the product of the eigenvalues, and sorting only permutes the factors. This implication detects the determinant obstruction in the counterexample.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/WassersteinMean.powerMean`
- Truth anchor: `D5/S3/Quantum/Matrix/WassersteinMean.wassersteinMean`
- Truth anchor: `D5/S3/Quantum/Matrix/WassersteinMean.weakLogMajorization`
- Truth anchor: `D5/S3/Quantum/Matrix/WassersteinMean.weakLogMajorization_det_le`
- Dependency: [D5/S3/Quantum/Hiai/PsiMeanTraceConcavity](../Hiai/PsiMeanTraceConcavity.md)
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](SpectralPower.md)
