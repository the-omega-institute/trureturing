# MatrixGaussianSourceDerivatives

## Abstract

Finite mixed complex coordinate derivatives of a positive matrix lattice Gaussian are the actual lattice monomial moments.

**Definition 1.1 (Ordered finite source differentiation).**

$$\operatorname{sourcePartial}\left(\operatorname{cons}\left(i, is\right), f, z\right) = \operatorname{derivAtZero}\left(t\mapsto\operatorname{sourcePartial}\left(is, f, z + t \cdot \operatorname{basisVector}\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Fourier/MatrixGaussianSourceDerivatives.sourcePartial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty list returns f(z). Prepending coordinate i differentiates the remaining function along z+t e_i at t=0. Coordinates may repeat. An empty rank admits only the empty list.

**Theorem 1.2 (Every finite mixed source derivative commutes with the lattice sum).**

$$\forall r \in N,\; \forall A \in \operatorname{RealMatrix}\left(r\right),\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(\forall b \in \mathbb{C},\; 0 < \operatorname{re}\left(b\right) \Rightarrow \left(\forall is \in \operatorname{List}\left(\operatorname{Fin}\left(r\right)\right),\; \forall z \in \operatorname{Fin}\left(r\right) \to \mathbb{C},\; \operatorname{sourcePartial}\left(is, z\mapsto\operatorname{tsum}\left(a:\operatorname{Fin}\left(r\right) \to Z\mapsto\operatorname{latticeSourceMap}\left(A, b, a, z\right)\right), z\right) = \operatorname{tsum}\left(a:\operatorname{Fin}\left(r\right) \to Z\mapsto\operatorname{listProduct}\left(is, i\mapsto\operatorname{castComplex}\left(\operatorname{a}\left(i\right)\right)\right) \cdot \operatorname{latticeSourceMap}\left(A, b, a, z\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussianSourceDerivatives.sourcePartial_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite rank, positive definite real Gram matrix A, complex b with positive real part, finite ordered list of coordinates and arbitrary complex source z, the mixed derivative is the sum of the product of the indicated integer coordinates times the original sourceful Gaussian. The proof bounds the coordinate product by the corresponding power of the lattice sup norm, applies the genuine polynomial Gaussian majorant on a bounded complex coordinate disk, and uses Mathlib.hasSum_deriv_of_summable_norm. A single list induction covers every finite order; no source summability or extraction assumption is imposed.

This is source differentiation at fixed Gaussian parameter b. It supplies finite source extraction, and makes no assertion of the still separate original mod-two theta S law or any fullK, Jacobi, VOA/CFT, BRST/string or AdS/CFT conclusion.

## References

- Truth anchor: `D5/S3/Fourier/MatrixGaussianSourceDerivatives.sourcePartial`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianSourceDerivatives.sourcePartial_tsum`
- Dependency: [D5/S3/Fourier/MatrixGaussianSourcePoisson](MatrixGaussianSourcePoisson.md)
