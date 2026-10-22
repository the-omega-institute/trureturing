# Finite Native Common Kernel

## Abstract

Native bivariate half-Fock product kernel

D is any finite-rank integral symmetric even-diagonal lattice datum; a,b are arbitrary charges. The oscillator input p is an arbitrary finite polynomial, not a homogeneous or truncated state. S_ab is the actual substitution X(i,k) -> C(X(i,k))-C(B(a,e_i))X0^(2k+1)-C(B(b,e_i))X1^(2k+1). J_ab[u,v](p) sums its actual finite support eta, multiplying coeff_eta(S_ab(p)) by halfCreationCoeff(a,u+eta0) halfCreationCoeff(b,v+eta1). Negative creation indices are zero. The bivariate convolution is formed from the delivered native creation coefficients and finite polynomial support.

**Theorem 1.1 (Actual finite translation composition).**

$$\operatorname{PairTranslationComposition}\left(D, a, b, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.pair_translation_composition` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Apply the delivered native halfTranslatedPolynomial for b, then translate its oscillator coefficients by S_a0 and evaluate its formal variable at X1. The result is exactly S_ab(p). Constants, polynomial addition and multiplication by each oscillator variable prove this equality. This finite composition is used in the two-coordinate creator recurrence.

**Theorem 1.2 (Constant readout).**

$$\operatorname{ConstantKernel}\left(D, a, b, u, v, c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.kernel_constant` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every complex c, J_ab[u,v](C(c))=C(c) halfCreationCoeff(a,u) halfCreationCoeff(b,v). The constant readout supplies the vacuum step of the ordered-product and branch-exchange proofs.

**Theorem 1.3 (Two-coordinate recurrence).**

$$\operatorname{CreatorKernel}\left(D, a, b, u, v, p, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.kernel_creator` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For each native index i=(colour,k), put omega_i=2k+1. Then J_ab[u,v](X_i p)=X_i J_ab[u,v](p)-B(a,e_colour) J_ab[u+omega_i,v](p) -B(b,e_colour) J_ab[u,v+omega_i](p). This recurrence is consumed by the universal branch-exchange and actual native product proofs, with no factor two in either translation.

**Theorem 1.4 (Rectangular lower bounds).**

$$\operatorname{RectangularSupport}\left(D, a, b, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_rectangular_support` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D,a,b,p there exist integers A,B such that for all integers u,v, u<A or v<B implies J_ab[u,v](p)=0. One can take A=-sup_eta eta0 and B=-sup_eta eta1 over the actual finite support of S_ab(p). Each supported summand then has a negative native creation index. The zero polynomial and empty support are included.

**Theorem 1.5 (Both ordered rays are finite).**

$$\operatorname{FiniteOrderedRays}\left(D, a, b, u, v, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_ordered_finite_support` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D,a,b,u,v,p, both r -> J_ab[u+r,v-r](p) and r -> J_ab[u-r,v+r](p), r in N, have finite support. The second coordinate bounds the first ray; the first coordinate bounds the second. These statewise bounds precede every finsum distribution or reindexing.

**Theorem 1.6 (Branch exchange).**

$$\operatorname{J}\left(a, b, u, v, p\right)=\operatorname{J}\left(b, a, v, u, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_branch_exchange` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D,a,b,u,v,p, J_ab[u,v](p)=J_ba[v,u](p). Constants use commutativity of actual creation polynomials; arbitrary input follows from polynomial addition and the actual two-coordinate creator recurrence.

Classical twisted-lattice construction, with zero novelty claim. This kernel is not a twisted Jacobi certificate, a physical iterate, or an orbifold reconstruction. The corresponding charged tensor fields use the actual ground representation selected from actual_twisted_ground_representation D hu, with hu:IsUnit D.G.det; the oscillator kernel itself needs no hu.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_branch_exchange`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_ordered_finite_support`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_rectangular_support`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.kernel_constant`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.kernel_creator`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.pair_translation_composition`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualProductKernel](LatticeActualProductKernel.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution](LatticeHalfFockBivariateConvolution.md)
