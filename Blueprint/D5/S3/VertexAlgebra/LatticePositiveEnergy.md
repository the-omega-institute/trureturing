# Actual Integral Energy and Finite Oscillator Sublevels

## Abstract

Exact integral half-norm identities and infinite-label oscillator counting on the actual lattice.

D is ordinary LatticeGeneratingFieldLocality.LatticeData: any natural rank, including zero, with an integral symmetric Gram matrix G and even diagonal. Charge(D)=Fin(rank(D))->Z; Index(D)=Fin(rank(D)) x N; Exponent(D)=Index(D)->_0 N. The actual Carrier(D) is the finite-support charge sum of complex multivariate polynomials in Index(D). A label is (alpha,d), and its actual basis vector is single(alpha,monomial(d,1)). Write q_D(alpha)=B_D(alpha,alpha)/2 in Z, w(d)=sum_x (x.2+1)*d(x), and E_D(alpha,d)=q_D(alpha)+w(d) in Z. Geometric positivity means exactly hD: Matrix.PosDef(G.map(Int.cast:Z->R)); it is supplied only where stated. There is no positive-rank, integral determinant-unit, unimodularity or assumed finite-grade premise.

Every declaration described here is publicly named in D5.S3.VertexAlgebra.LatticePositiveEnergy, including declarations whose source module has a different file name. Definition bindings expose the actual data or constructed equivalences; the substantive completion consists of the proved positivity, finiteness, decomposition and actual-operator theorems.

The five lower-matrix/cocycle helpers are exact consumed bodies from the public LatticeTwistedGroundRealization.SignQuotient generation source, SHA256 f7032c03d6edd67435d766c9e0c503774dd50561742e3c6e95f722b657f47781. They are used in two_chargeEnergy and subsequent positivity, not unused scaffolding. The finite oscillator encoding adapts the source-only advisory probe and PolynomialFockLZeroSpectrum; no historical probe object is claimed.

**Definition 1.1 (Integral lower Gram matrix).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.lowerMatrix`

*Formalization.* `D5/S3/VertexAlgebra/LatticePositiveEnergy.lowerMatrix` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The strict lower triangle of G is completed with the integral halfDiagonal on its diagonal. This is the consumed realized-cocycle helper, with its proof source retained exactly.

**Theorem 1.2 (Cocycle as a matrix contraction).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.lower_matrix_formula`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticePositiveEnergy.lower_matrix_formula` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For all charges alpha,beta, lowerCocycleExponent(D,alpha,beta) is sum_i sum_j alpha_i lowerMatrix(D)_(ij) beta_j. No positivity is needed.

**Theorem 1.3 (Integral symmetrization).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.lower_matrix_symmetrization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticePositiveEnergy.lower_matrix_symmetrization` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

lowerMatrix(D)+transpose(lowerMatrix(D))=G. Symmetry and even diagonal are fields of D, not additional assumptions.

**Theorem 1.4 (Cocycle recovers the bilinear form).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.integral_cocycle_symmetrization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticePositiveEnergy.integral_cocycle_symmetrization` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For all charges alpha,beta, c(alpha,beta)+c(beta,alpha)=B_D(alpha,beta). This identity is consumed in the exact integral half-norm proof.

**Theorem 1.5 (Exact integral half-norm).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.integral_cocycle_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticePositiveEnergy.integral_cocycle_square` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

c(alpha,alpha)=B_D(alpha,alpha)/2 in Z, for every ordinary D and charge alpha. Division is integral, and the preceding symmetrization establishes exact divisibility.

**Definition 1.6 (Actual oscillator exponent type).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.Exponent`

*Formalization.* `D5/S3/VertexAlgebra/LatticePositiveEnergy.Exponent` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Exponent(D) is the finitely supported natural exponent function on Fin(rank(D)) x N. The index type is infinite when rank is positive.

**Definition 1.7 (Actual all-charge monomial labels).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.Label`

*Formalization.* `D5/S3/VertexAlgebra/LatticePositiveEnergy.Label` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Label(D)=Charge(D) x Exponent(D). This type indexes the entire actual carrier basis, without a finite-variable truncation.

**Definition 1.8 (Integral charge energy).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy`

*Formalization.* `D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

chargeEnergy(D,alpha) is B_D(alpha,alpha)/2 in Z. The following cocycle and doubling identities prove this is the exact half-norm.

**Theorem 1.9 (Charge energy is realized cocycle square).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy_cocycle`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy_cocycle` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

q_D(alpha)=lowerCocycleExponent(D,alpha,alpha), for every charge alpha and ordinary D, including rank zero.

**Theorem 1.10 (No lost half-norm remainder).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.two_chargeEnergy`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticePositiveEnergy.two_chargeEnergy` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

2*q_D(alpha)=B_D(alpha,alpha) in Z. Evenness is proved from the consumed realized integral cocycle, not a divisibility axiom.

**Theorem 1.11 (All integral charge squares are even).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.bilinear_even`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticePositiveEnergy.bilinear_even` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Even(B_D(alpha,alpha)) for every charge alpha follows from the exact doubling identity. No positivity or unimodularity is used.

**Theorem 1.12 (Zero charge has zero energy).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy_zero` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

q_D(0)=0 unconditionally for every ordinary D.

**Theorem 1.13 (Real Gram positivity controls integral charges).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.bilinear_positive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticePositiveEnergy.bilinear_positive` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Under hD and alpha!=0, 0<B_D(alpha,alpha) in Z. The real positive-definite quadratic form is evaluated on the real cast of the integral charge.

**Theorem 1.14 (Derived nonnegative integral charge energy).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy_nonneg` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Under hD, q_D(alpha)>=0 for all charges. The proof handles alpha=0 separately and uses positive square plus exact doubling for nonzero alpha.

**Theorem 1.15 (Only the zero charge has zero energy).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy_eq_zero_iff` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Under hD, q_D(alpha)=0 iff alpha=0. This conclusion includes arbitrary finite rank and rank zero.

**Definition 1.16 (Frequency-weighted oscillator energy).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.oscillatorEnergy`

*Formalization.* `D5/S3/VertexAlgebra/LatticePositiveEnergy.oscillatorEnergy` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

w(d)=Finsupp.weight(fun (i,k)=>k+1,d) in N. The polynomial variable (i,k) represents positive frequency k+1.

**Definition 1.17 (Full integral lattice energy).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.energy`

*Formalization.* `D5/S3/VertexAlgebra/LatticePositiveEnergy.energy` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

E_D(alpha,d)=q_D(alpha)+(w(d):Z). This grades all charge sectors of the actual carrier.

**Theorem 1.18 (Finite sublevels despite infinite labels).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.oscillatorLeFinite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticePositiveEnergy.oscillatorLeFinite` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every D and N:N, {d:Exponent(D) | w(d)<=N} is finite, without hD. An occupied frequency obeys k+1<=N; every exponent is <=N. Restriction injects this sublevel into (Fin(rank(D)) x Fin(N))->Fin(N+1). N=0 and rank zero are included. No finite Index(D) instance is assumed.

**Theorem 1.19 (Zero oscillator energy is the constant monomial).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.oscillatorEnergy_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticePositiveEnergy.oscillatorEnergy_eq_zero_iff` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every ordinary D, w(d)=0 iff d=0, because every frequency weight is positive.

**Theorem 1.20 (Full energy is nonnegative).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.energy_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticePositiveEnergy.energy_nonneg` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Under hD, E_D(alpha,d)>=0 for every label, by nonnegative charge energy and natural oscillator weight.

**Theorem 1.21 (Unique zero-energy label).**

Lean statement: `D5/S3/VertexAlgebra/LatticePositiveEnergy.energy_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticePositiveEnergy.energy_eq_zero_iff` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Under hD, E_D(alpha,d)=0 iff (alpha,d)=(0,0). Both nonnegative summands must vanish.

Bakalov-Kac, Twisted Modules over Lattice Vertex Algebras, arXiv math/0402315v1 (19 February 2004): section 4.1, printed/PDF page 8, equations (4.3)-(4.5), gives the charge/Fock carrier; page 9, Theorem 4.1 and (4.16), gives the dual-basis conformal vector; page 4, Definition 2.2 and (2.23)-(2.24), gives the conformal grading convention. These are construction and convention locators, not proofs of the new coercivity and counting results.

Borcherds, Vertex algebras, Kac-Moody algebras, and the Monster, PNAS 83 (1986), 3068-3071: the author-hosted retypesetting, section 2, printed/PDF page 2, specifies deg(e^alpha)=B(alpha,alpha)/2 and the frequency-weighted oscillator degree. Its SHA256 is 822e39a2ec7bd33ad81193b06b7a66ae89abcec43c4cb7974d4bc513c3fce5b5. It has no equation numbers there; no correspondence to a particular original journal page is asserted.

Dong-Li-Mason, Regularity of rational vertex operator algebras, arXiv q-alg/9508018v1 (24 August 1995), printed/PDF page 3, Definition 2.1, supplies the ordinary-module finite-dimensional eigenspace and lower-truncation convention. Those properties are derived here from hD, rather than assumed. Its regularity theorem is not proved by this unit.

Lean 4.33.0 and the declared Mathlib pin db584cd6d46c92f209a44c0f1c829460d327499d supply the actual imported finite-support, basis, compactness and matrix APIs. Mathlib adaptations retain Apache-2.0 and the original authorship. Exact producer References, SourceInputs, SourceAdaptation, MathlibLocators and source/object/import hashes are delivered with this staging; the pin is inherited from sealed toolchain evidence and was not established by a fresh Git inspection.

This unit supplies the actual lattice carrier with a positive finite energy grading and identifies it with the actual Sugawara L_0 eigenspaces under the explicit inverse pair. It does not construct a PCT involution, Hermitian form, analytic Hilbert completion, twisted vertex algebra, Monster realization, fusion category, anomaly, string theory or AdS/CFT. The complete supplier Virasoro theorem is a separate result and is not replaced by these modules.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.Exponent`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.Label`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.bilinear_even`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.bilinear_positive`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy_cocycle`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy_eq_zero_iff`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy_nonneg`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy_zero`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.energy`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.energy_eq_zero_iff`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.energy_nonneg`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.integral_cocycle_square`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.integral_cocycle_symmetrization`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.lowerMatrix`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.lower_matrix_formula`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.lower_matrix_symmetrization`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.oscillatorEnergy`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.oscillatorEnergy_eq_zero_iff`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.oscillatorLeFinite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticePositiveEnergy.two_chargeEnergy`
- Dependency: [D5/S3/VertexAlgebra/LatticeGeneratingFieldLocality](LatticeGeneratingFieldLocality.md)
