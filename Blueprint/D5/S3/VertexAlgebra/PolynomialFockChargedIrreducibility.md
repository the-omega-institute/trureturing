# Charged Polynomial Fock Irreducibility

## Abstract

The actual charged polynomial Heisenberg modes have only zero and full invariant subspaces.

Let F=C[X_0,X_1,...]. For every complex charge r, alpha^(r)_0 is r times the identity, alpha^(r)_(j+1) is (j+1) times partial differentiation in X_j, and alpha^(r)_(-j-1) is multiplication by X_j, for every natural j. The nonzero modes are the existing concrete polynomial Fock modes. Write chargedMode(r,n,p)=alpha^(r)_n p.

**Theorem 1.1 (Every invariant complex subspace is zero or full).**

$$\forall r\in\mathbb{C}, \forall S\in\operatorname{Submodule}\left(\mathbb{C}, F\right),\ (\forall n\in\mathbb{Z}, \forall p\in F, p\in S\Rightarrow\operatorname{chargedMode}\left(r, n, p\right)\in S)\Rightarrow S=\{0\}\lor S=F$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockChargedIrreducibility.charged_modes_irreducible` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *A Note on Free Bosonic Vertex Algebra and its Conformal Vectors*. URL: <https://arxiv.org/abs/hep-th/9704060v1>.

*Commentary.*

There is no restriction on the charge or the dimension of the subspace. Invariance is required for every integer mode and every polynomial in the subspace. It is not an assumed irreducible representation or an assumed vertex-algebra module.

In a nonzero invariant subspace, select a nonzero polynomial of least total degree. Positive-mode invariance and the invertibility of j+1 give closure under every partial derivative. A nonzero partial derivative would have smaller total degree, so all partial derivatives of the selected polynomial vanish. Characteristic zero makes it a nonzero constant. Scaling gives the unit; negative modes then create every monomial, and linearity gives the whole polynomial algebra.

Matsuo-Nagatomo, Section 2.2, printed pages 20-21, states the charged polynomial representation and its irreducibility. The identification is x_(j+1)=X_j. The charge r differs from a conformal background-charge parameter. This result concerns Heisenberg modes; it does not establish Virasoro irreducibility, charged all-state module Jacobi, intertwiners or fusion, a Monster realization, string theory or AdS/CFT geometry.

## References

- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockChargedIrreducibility.charged_modes_irreducible`
- Dependency: [D5/S3/Quantum/Algebra/ConditionalPolynomialRigidity](../Quantum/Algebra/ConditionalPolynomialRigidity.md)
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockSugawaraSupport](PolynomialFockSugawaraSupport.md)
