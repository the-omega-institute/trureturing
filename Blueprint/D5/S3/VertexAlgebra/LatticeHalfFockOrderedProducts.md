# Native Product Expansions

## Abstract

Supported ordered native half-Fock products

For arbitrary D,a,b,p and integers k,l, write q_a=B(a,a), R_a[k]=oscillatorCoefficient D a (k-q_a), and h_g[r]=coeff_r(halfContraction D a b), g=B(a,b). R is notation for the delivered native endomorphism, not a replacement implementation. half_creation_coefficient_transport supplies the exact translated creation coefficient. The bivariate common kernel supplies finite supports before sums are distributed. Polynomial induction uses the native oscillator creator recurrence and both independent kernel shifts.

**Theorem 1.1 (First ordered product).**

$$\operatorname{FirstOrderedProduct}\left(D, a, b, k, l, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.native_ordered_product` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Exactly R_a[k](R_b[l]p)=sum_(r>=0) h_g[r] J_ab[k+r,l-r](p). The sum is statewise finite on every arbitrary polynomial p. No sign restriction on g, occupation cutoff, analytic BCH identity, or unproved infinite operator rearrangement is used.

**Theorem 1.2 (Reverse ordered product).**

$$\operatorname{ReverseOrderedProduct}\left(D, a, b, k, l, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.native_reverse_ordered_product` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Exactly R_b[l](R_a[k]p)=sum_(r>=0) h_g[r] J_ab[k-r,l+r](p). Exchange of the actual kernel and symmetry of the actual bilinear form identify this with the first ordered theorem with charges and coefficient indices exchanged.

**Theorem 1.3 (First product on every actual tensor state).**

$$\operatorname{TensorFirstProduct}\left(D, hu, a, b, e, f, state\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.charged_tensor_ordered_product` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D,hu,a,b,e,f,state, A_a[e](A_b[f]state)=c_a c_b sum_r h_g[r] TensorProduct.map(J_ab[e+q_a+r,f+q_b-r],U_a U_b)state. Actual tensor induction proves rectangular bounds and pointwise finite support before the sum defines a linear readout. The pure-tensor formula follows directly from the delivered native oscillator product; addition extends it to all unrestricted ActualTensor states.

**Theorem 1.4 (Reverse product on every actual tensor state).**

$$\operatorname{TensorReverseProduct}\left(D, hu, a, b, e, f, state\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.charged_tensor_reverse_ordered_product` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D,hu,a,b,e,f,state, A_b[f](A_a[e]state)=c_a c_b sum_r h_g[r] TensorProduct.map(J_ba[f+q_b+r,e+q_a-r],U_b U_a)state. Native branch exchange identifies that oscillator kernel with J_ab[e+q_a-r,f+q_b+r]. The actual ground action retains its reversed order; it is not silently replaced by U_a U_b.

For the actual tensor fields, hu:IsUnit D.G.det selects groundRank, groundRepresentation and groundAction from actual_twisted_ground_representation D hu. chargedCoefficient(a,e) is c_a times TensorProduct.map(oscillatorCoefficient(a,e),groundAction(a)), c_a=2^(-q_a). Consequently the unshifted first index is k=e+q_a, the second is l=f+q_b, and the ordered ground action is U_a U_b, not an assumed commuting action.

Physical coordinates are z=x^2,w=y^2. The physical locality certificate still requires the actual finite j=0..abs(g) binomial commutator sum with indices e-2(N-j),f-2j. Both cover factors 1-s and 1+s must be cleared: m=(-g).toNat,n=g.toNat and (1-s)^m(1+s)^n h_g=(1-s)^n(1+s)^m. Positive g retains an opposite-sheet pole. Rational-function equality is not equality of the two unregularized iota expansions. Physical coefficient locality, twisted Jacobi, physical derivatives shifting cover exponents by two, all-order ordinary-field iterates and orbifold intertwiners remain separate proof obligations. Scalar c_a matches leading physical iterate normalization; locality alone does not determine it. Classical provenance, zero novelty claim; no full Leech, Monster, fusion, string or AdS realization follows.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.charged_tensor_ordered_product`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.charged_tensor_reverse_ordered_product`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.native_ordered_product`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.native_reverse_ordered_product`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockGroundProducts](LatticeHalfFockGroundProducts.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockProductKernel](LatticeHalfFockProductKernel.md)
