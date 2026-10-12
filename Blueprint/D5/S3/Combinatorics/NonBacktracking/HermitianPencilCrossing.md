# Hermitian pencil crossing

## Abstract

A Hermitian affine pencil becomes singular between endpoint subspaces with opposite ordered-eigenvalue signs.

For Hermitian matrices A and B, the pencil A minus t times B has ordered eigenvalues that vary continuously with the real parameter t. If a subspace is nonpositive at the left endpoint and another subspace of the complementary dimension is positive at the right endpoint, the indexed eigenvalue crosses zero before the right endpoint.

**Theorem 1.1 (A singular point of the pencil).**

$$\forall I \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall A \in \operatorname{Matrix}\left(I, I, \mathrm{Complex}\right),\; \forall B \in \operatorname{Matrix}\left(I, I, \mathrm{Complex}\right),\; \operatorname{Matrix}.\operatorname{IsHermitian}\left(A\right) \Rightarrow \left(\operatorname{Matrix}.\operatorname{IsHermitian}\left(B\right) \Rightarrow \left(\forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; a \le b \Rightarrow \left(\forall k \in \operatorname{Fin}\left(\operatorname{Fintype}.\operatorname{card}\left(I\right)\right),\; \forall W \in \operatorname{Submodule}\left(\mathrm{Complex}, \operatorname{EuclideanSpace}\left(\mathrm{Complex}, I\right)\right),\; \forall V \in \operatorname{Submodule}\left(\mathrm{Complex}, \operatorname{EuclideanSpace}\left(\mathrm{Complex}, I\right)\right),\; \operatorname{Module}.\operatorname{finrank}\left(\mathrm{Complex}, W\right) + \operatorname{Fin}.\operatorname{val}\left(k\right) + 1 > \operatorname{Fintype}.\operatorname{card}\left(I\right) \Rightarrow \left(\operatorname{Module}.\operatorname{finrank}\left(\mathrm{Complex}, V\right) = \operatorname{Fin}.\operatorname{val}\left(k\right) + 1 \Rightarrow \left(\left(\forall x \in \operatorname{EuclideanSpace}\left(\mathrm{Complex}, I\right),\; x \in W \Rightarrow \operatorname{RCLike}.\operatorname{re}\left(\operatorname{inner}\left(\mathrm{Complex}, \operatorname{Matrix}.\operatorname{toEuclideanLin}\left(A - \operatorname{Complex}.\operatorname{ofReal}\left(a\right) \cdot B\right)\left(x\right), x\right)\right) \le 0\right) \Rightarrow \left(\left(\forall x \in \operatorname{EuclideanSpace}\left(\mathrm{Complex}, I\right),\; x \in V \Rightarrow \left(x \ne 0 \Rightarrow 0 < \operatorname{RCLike}.\operatorname{re}\left(\operatorname{inner}\left(\mathrm{Complex}, \operatorname{Matrix}.\operatorname{toEuclideanLin}\left(A - \operatorname{Complex}.\operatorname{ofReal}\left(b\right) \cdot B\right)\left(x\right), x\right)\right)\right)\right) \Rightarrow \left(\exists t \in \mathrm{Real},\; t \in \operatorname{Set}.\operatorname{Ico}\left(a, b\right) \land \left(\exists x \in I \to \mathrm{Complex},\; x \ne 0 \land \operatorname{Matrix}.\operatorname{mulVec}\left(A - \operatorname{Complex}.\operatorname{ofReal}\left(t\right) \cdot B, x\right) = 0\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NonBacktracking/HermitianPencilCrossing.pencil_singular_of_subspaces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Mulas; D. Zhang; G. Zucal (2024). *There is no going back: Properties of the non-backtracking Laplacian*. DOI: [10.1016/j.laa.2023.10.014](https://doi.org/10.1016/j.laa.2023.10.014). URL: <https://arxiv.org/abs/2303.00373v2>.

*Commentary.*

The dimension inequality forces the two spectral subspaces to intersect trivially at the left endpoint, while the positive endpoint subspace supplies the opposite sign. Continuity of the selected ordered eigenvalue gives a parameter t in the half-open interval and a nonzero kernel vector.

## References

- Truth anchor: `D5/S3/Combinatorics/NonBacktracking/HermitianPencilCrossing.pencil_singular_of_subspaces`
- Dependency: [D5/S3/SpectralTopology/HermitianEigenvaluePerturbation](../../SpectralTopology/HermitianEigenvaluePerturbation.md)
