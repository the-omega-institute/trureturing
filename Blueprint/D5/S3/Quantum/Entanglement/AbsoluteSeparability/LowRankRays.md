# Low-rank separable rays

## Abstract

The identity plus twice a normalized bipartite rank-one projector is a finite sum of positive semidefinite Kronecker products.

Write R_x = xx* and let the separable cone consist of finite sums of Kronecker products of positive semidefinite matrices. For every complex vector on Fin m times Fin n with sum of squared coordinate norms one, the matrix I + 2 R_x belongs to this cone. The conclusion includes all finite dimensions; the normalization cannot hold when either index set is empty.

**Theorem 1.1 (A normalized rank-one ray).**

$$\forall (m:\mathbb{N}), \forall (n:\mathbb{N}), \forall (psi:(Fin\left(m\right)\times Fin\left(n\right))\to \mathbb{C}), (\sum_{ij\in Fin\left(m\right)\times Fin\left(n\right)} \left\lVert psi\left(ij\right) \right\rVert^{2}=1)\Rightarrow separableCone\left(I+2\cdot R\left(psi\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRays.separableCone_one_add_two_rankOne` (`✓ std3`). ∎

*Citation.* Guifré Vidal and Rolf Tarrach (1999). *Robustness of entanglement*. DOI: [10.1103/PhysRevA.59.141](https://doi.org/10.1103/PhysRevA.59.141). URL: <https://doi.org/10.1103/PhysRevA.59.141>.

*Commentary.*

Vidal--Tarrach Eq. (41), printed page 15, gives random robustness mn a₁a₂ for a normalized pure state with largest Schmidt coefficients a₁,a₂. Since 2a₁a₂ ≤ a₁ squared + a₂ squared ≤ 1, the matrix R_x + one half I is separable. The formal statement is the consequence scaled by two, I + 2 R_x, in the finite-sum separable cone.

Compactness of the two unit spheres provides a product pair u,v maximizing the real overlap with the vector. If alpha is the maximal overlap and lambda = alpha squared, the two partial contractions equal alpha u and alpha v. The same maximum bounds the reduced matrix by lambda I.

When lambda is at most one half, twice the finite product-vector average represents 2 R_x plus a reduced-matrix term. The remaining factor I - 2 rho is positive semidefinite.

When lambda is at least one half, subtract alpha u tensor v to obtain chi, orthogonal to both selected factors. Put U = R_u, V = R_v, P = I - U and Q = I - V. The squared norm of chi is 1 - lambda, and compression of the Gram bound proves K = (1 - lambda) Q - rho_chi positive semidefinite. The projected finite average is corrected by U tensor (V + Q - 4 lambda rho_chi) and P tensor (Q - 2 rho_chi). The correction factors equal V + (2 lambda - 1) squared Q + 4 lambda K and (2 lambda - 1) Q + 2 K, respectively.

Every averaged vector is a product vector. The proof uses finite moments and compactness, without a Schmidt decomposition. Separability here is the algebraic cone property of finite matrices.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRays.separableCone_one_add_two_rankOne`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRaysAverages](LowRankRaysAverages.md)
- Dependency: [D5/S3/Resource/SeparableConeResidualWitness](../../../Resource/SeparableConeResidualWitness.md)
