# Native Half-Fock Forward Ordered Products

## Abstract

Full forward ordered products of native half-Fock coefficients

Let D be any integral symmetric even-diagonal lattice datum, with arbitrary finite rank. The charges a,b are arbitrary integer-valued lattice vectors. The oscillator algebra is the entire MvPolynomial(Fin(D.rank) times N,C), including every inhomogeneous polynomial. No determinant, positivity, charge-pairing sign, or mode cutoff is assumed. Put q(a)=B(a,a) and omega(i,j)=2j+1. All external indices s,t range independently over the integers.

Write C_a[n]=halfCreationCoeff D a n, with C_a[n]=0 for n<0, and Q_a(p)=halfTranslatedPolynomial D a p. Q_a replaces X(i,j) by X(i,j)-B(a,e_i)x^(2j+1). The bivariate pairTranslation replaces it by X(i,j)-B(a,e_i)x^(2j+1)-B(b,e_i)y^(2j+1). pairConvolution at (s,t) sends a monomial c x^u y^v to c C_a[s+u] C_b[t+v]. Their composition is the complex-linear commonKernel, denoted K(D,a,b,s,t,p). The two translation variables represent inverse cover coordinates, accounting for the positive offsets.

**Theorem 1.1 (Successive translations).**

$$\forall D:LatticeData, a:\operatorname{Charge}\left(D\right), b:\operatorname{Charge}\left(D\right), p:\operatorname{Oscillator}\left(D\right), \operatorname{secondTranslationLift}\left(D, a, \operatorname{Q}\left(D, b, p\right)\right)=\operatorname{pairTranslation}\left(D, a, b, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.pair_translation_composition` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The complete parameters are D,a,b,p as above. secondTranslationLift applies the first translation to every coefficient of Q_b(p) and sends its polynomial variable to y. This equals the simultaneous pairTranslation for every polynomial, by equality on constants, sums and multiplication by each generator.

**Theorem 1.2 (Kernel on constants).**

$$\forall D:LatticeData, a:\operatorname{Charge}\left(D\right), b:\operatorname{Charge}\left(D\right), s:\mathbb{Z}, t:\mathbb{Z}, c:\mathbb{C}, \operatorname{K}\left(D, a, b, s, t, \operatorname{C}\left(c\right)\right)=\operatorname{C}\left(c\right) \operatorname{creation}\left(D, a, s\right) \operatorname{creation}\left(D, b, t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.kernel_constant` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every complex scalar c, the kernel of C(c) is C(c) C_a[s] C_b[t]. This follows from the constant bivariate monomial and is used in the vacuum contraction calculation.

**Theorem 1.3 (Both creator shifts).**

$$\forall D:LatticeData, a:\operatorname{Charge}\left(D\right), b:\operatorname{Charge}\left(D\right), s:\mathbb{Z}, t:\mathbb{Z}, p:\operatorname{Oscillator}\left(D\right), i:\operatorname{Index}\left(D\right), \operatorname{K}\left(D, a, b, s, t, \operatorname{X}\left(i\right)p\right)=\operatorname{X}\left(i\right)\operatorname{K}\left(D, a, b, s, t, p\right)-\operatorname{B}\left(a, \operatorname{unitCharge}\left(D, \operatorname{fst}\left(i\right)\right)\right) \operatorname{K}\left(D, a, b, s+\operatorname{omega}\left(D, i\right), t, p\right)-\operatorname{B}\left(b, \operatorname{unitCharge}\left(D, \operatorname{fst}\left(i\right)\right)\right) \operatorname{K}\left(D, a, b, s, t+\operatorname{omega}\left(D, i\right), p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.kernel_creator` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every oscillator index i, multiplication by X(i) has two independent odd-frequency shifts in the common kernel. The scalar products act by complex scalar multiplication. Multiplying a bivariate polynomial by x^r or y^r shifts the corresponding convolution index by r.

**Theorem 1.4 (Separate lower bounds).**

$$\forall D:LatticeData, a:\operatorname{Charge}\left(D\right), b:\operatorname{Charge}\left(D\right), p:\operatorname{Oscillator}\left(D\right), \exists u:\mathbb{Z}, v:\mathbb{Z}, \forall s:\mathbb{Z}, t:\mathbb{Z}, (s<u\lor t<v)\implies\operatorname{K}\left(D, a, b, s, t, p\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.common_kernel_rectangular_support` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The finite support of pairTranslation(p) bounds its x and y exponents separately. Take u and v to be the negatives of the two support suprema. Outside this rectangle one creation index is negative in every summand, so the common kernel vanishes. The zero polynomial and rank zero are included.

**Theorem 1.5 (Finite support along both diagonals).**

$$\forall D:LatticeData, a:\operatorname{Charge}\left(D\right), b:\operatorname{Charge}\left(D\right), s:\mathbb{Z}, t:\mathbb{Z}, p:\operatorname{Oscillator}\left(D\right), \operatorname{HasFiniteSupport}\left(\operatorname{lambda}\left(d:\mathbb{N}, \operatorname{K}\left(D, a, b, s+d, t-d, p\right)\right)\right)\land \operatorname{HasFiniteSupport}\left(\operatorname{lambda}\left(d:\mathbb{N}, \operatorname{K}\left(D, a, b, s-d, t+d, p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.common_kernel_ordered_finite_support` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For fixed s,t,p, both nonnegative-degree diagonal restrictions have finite support. The forward bound comes from t-d<v, and the opposite bound from s-d<u. Multiplying by contraction coefficients preserves this support and justifies every finsum distribution.

Set kappa(D,a,b,d)=coeff_d(halfContraction D a b), where halfContraction is rescale(-1,binomialSeries(B(a,b))) times binomialSeries(-B(a,b)), the expansion of ((1-z)/(1+z))^(B(a,b)). This is the original half-Fock contraction with both cover-pole factors. Write A(a,s)=oscillatorCoefficient D a (s-q(a)).

**Theorem 1.6 (Full forward composed-action identity).**

$$\forall D:LatticeData, a:\operatorname{Charge}\left(D\right), b:\operatorname{Charge}\left(D\right), s:\mathbb{Z}, t:\mathbb{Z}, p:\operatorname{Oscillator}\left(D\right), \operatorname{A}\left(D, a, s, \operatorname{A}\left(D, b, t, p\right)\right)=\operatorname{finsum}\left(d:\mathbb{N}, \operatorname{kappa}\left(D, a, b, d\right) \operatorname{K}\left(D, a, b, s+d, t-d, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.native_ordered_product` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For all D,a,b,s,t,p without further hypotheses, A(a,s)(A(b,t)p) equals the supported sum over d:N of kappa(D,a,b,d) times K(D,a,b,s+d,t-d,p). For a constant polynomial, native half_creation_coefficient_transport evaluates each translated creation coefficient exactly. Both the actual composite and the expansion are linear. The existing native oscillatorCoefficient_X_mul identity gives the same two creator shifts as kernel_creator. Structural induction on the full polynomial algebra therefore establishes the equality. No product, locality, Jacobi or desired action identity is supplied as an assumption.

The reverse ordered-product law, charged ground-product and tensor-product laws, diagonal two-step locality, and the full native BPZ statement remain unproved here. This forward oscillator identity alone does not establish a VOA, a full CFT, fusion or anomaly laws, string dynamics, AdS/CFT, or a reconstruction of spacetime geometry.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.common_kernel_ordered_finite_support`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.common_kernel_rectangular_support`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.kernel_constant`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.kernel_creator`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.native_ordered_product`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.pair_translation_composition`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients](LatticeHalfFockChargedTensorCoefficients.md)
