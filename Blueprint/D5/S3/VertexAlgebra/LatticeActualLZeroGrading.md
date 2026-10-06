# Actual Sugawara Eigenspaces and Integer Mode Grading

## Abstract

Both inverse-Gram equations identify actual Sugawara eigenspaces with exact coefficient grades.

D is ordinary LatticeGeneratingFieldLocality.LatticeData: any natural rank, including zero, with an integral symmetric Gram matrix G and even diagonal. Charge(D)=Fin(rank(D))->Z; Index(D)=Fin(rank(D)) x N; Exponent(D)=Index(D)->_0 N. The actual Carrier(D) is the finite-support charge sum of complex multivariate polynomials in Index(D). A label is (alpha,d), and its actual basis vector is single(alpha,monomial(d,1)). Write q_D(alpha)=B_D(alpha,alpha)/2 in Z, w(d)=sum_x (x.2+1)*d(x), and E_D(alpha,d)=q_D(alpha)+w(d) in Z. Geometric positivity means exactly hD: Matrix.PosDef(G.map(Int.cast:Z->R)); it is supplied only where stated. There is no positive-rank, integral determinant-unit, unimodularity or assumed finite-grade premise.

Every declaration described here is publicly named in D5.S3.VertexAlgebra.LatticePositiveEnergy, including declarations whose source module has a different file name. Definition bindings expose the actual data or constructed equivalences; the substantive completion consists of the proved positivity, finiteness, decomposition and actual-operator theorems.

The actual operator is LatticeSugawaraConformal.sugawaraMode, and the actual state-field is LatticeAllStateField.Y. The supplier sugawaraMode_zero_single and oscillatorEuler_monomial give the basis action; LatticeActualConformalEnergy.fused_eigenstate_energy gives the actual mode-product law. These are imported results on the same carrier, not substitute energy operators. Both hHG and hGH remain explicit whenever H is supplied. Geometric positivity is only needed to derive a complex inverse pair and to obtain positive finite grades.

**Theorem 1.1 (Exact complex half-norm cast).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.chargeEnergy_complex_half`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.chargeEnergy_complex_half` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

(q_D(alpha):C)=(B_D(alpha,alpha):C)/2. The integral doubling theorem justifies the cast; no rounding or integral unit determinant is involved.

**Theorem 1.2 (Exact actual basis coordinates).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.carrierCoeffEquiv_basis`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.carrierCoeffEquiv_basis` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

carrierCoeffEquiv(D,carrierBasis(D,a))=single(a,1), for every actual label a.

**Theorem 1.3 (Actual Sugawara action on every basis vector).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.actualL0_basis`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.actualL0_basis` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Let H be any complex rank-by-rank matrix with hHG:H*gramComplex(D)=1 and hGH:gramComplex(D)*H=1. Under exactly these two equations, actual sugawaraMode(D,H,0) acts on carrierBasis(D,a) by (E_D(a):C). The supplier zero-mode and oscillator Euler theorems are consumed; hD is not a premise.

**Theorem 1.4 (Actual Sugawara action on arbitrary-state coefficients).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.actualL0_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.actualL0_coeff` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Under exactly hHG and hGH, the coefficient at any label a of actual L_0(v) equals (E_D(a):C) times the coefficient of v, for every actual v. v need not be homogeneous.

**Theorem 1.5 (Two-way actual eigenstate and grade criterion).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.actualL0_eigen_iff_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.actualL0_eigen_iff_grade` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Under exactly both inverse equations, for every n:Z and arbitrary actual v, sugawaraMode(D,H,0)(v)=(n:C)*v iff v belongs to grade(D,n). Both directions follow by actual coefficient separation; no eigenaction or grading compatibility is assumed.

**Theorem 1.6 (Exact all-integer actual eigenspaces).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.actualL0_eigenspace_eq_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.actualL0_eigenspace_eq_grade` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Under exactly hHG and hGH, the eigenspace of actual sugawaraMode(D,H,0) at (n:C) equals grade(D,n) for every integer n. Positivity is not needed for this equality; hD gives finiteness and negative vanishing separately.

**Theorem 1.7 (All-integer actual state-field mode closure).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.actual_mode_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.actual_mode_grade` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Under exactly both inverse equations, for all m,n,q:Z and actual a in grade(D,m), b in grade(D,n), ((Y(D,a))[[q]])(b) belongs to grade(D,m+n-q-1). The normalized q-mode is the Laurent coefficient at -q-1. This uses the actual Y and the sealed fused_eigenstate_energy theorem, not an assumed graded product.

**Theorem 1.8 (Real positivity supplies a complex inverse pair).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.complex_inverse_exists`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.complex_inverse_exists` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Under hD there exists a complex matrix H with H*gramComplex(D)=1 and gramComplex(D)*H=1. Real positive definiteness gives a nonzero real determinant, its complex cast is nonzero, and complex matrix inversion supplies both equations. There is no assertion that the integral determinant is a unit.

**Theorem 1.9 (PosDef alone gives actual integer mode closure).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.positive_actual_mode_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.positive_actual_mode_grade` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Under hD alone, all m,n,q:Z and actual a in grade(D,m), b in grade(D,n) satisfy ((Y(D,a))[[q]])(b) in grade(D,m+n-q-1). The proof obtains a complex inverse pair and applies actual_mode_grade. No H or unimodularity premise remains.

Bakalov-Kac, Twisted Modules over Lattice Vertex Algebras, arXiv math/0402315v1 (19 February 2004): section 4.1, printed/PDF page 8, equations (4.3)-(4.5), gives the charge/Fock carrier; page 9, Theorem 4.1 and (4.16), gives the dual-basis conformal vector; page 4, Definition 2.2 and (2.23)-(2.24), gives the conformal grading convention. These are construction and convention locators, not proofs of the new coercivity and counting results.

Borcherds, Vertex algebras, Kac-Moody algebras, and the Monster, PNAS 83 (1986), 3068-3071: the author-hosted retypesetting, section 2, printed/PDF page 2, specifies deg(e^alpha)=B(alpha,alpha)/2 and the frequency-weighted oscillator degree. Its SHA256 is 822e39a2ec7bd33ad81193b06b7a66ae89abcec43c4cb7974d4bc513c3fce5b5. It has no equation numbers there; no correspondence to a particular original journal page is asserted.

Dong-Li-Mason, Regularity of rational vertex operator algebras, arXiv q-alg/9508018v1 (24 August 1995), printed/PDF page 3, Definition 2.1, supplies the ordinary-module finite-dimensional eigenspace and lower-truncation convention. Those properties are derived here from hD, rather than assumed. Its regularity theorem is not proved by this unit.

Lean 4.33.0 and the declared Mathlib pin db584cd6d46c92f209a44c0f1c829460d327499d supply the actual imported finite-support, basis, compactness and matrix APIs. Mathlib adaptations retain Apache-2.0 and the original authorship.

The consumed Sugawara architecture retains Kalle Kytola, VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4, Apache-2.0. The actual field normal-product and integer residue interfaces retain Scott Carnahan, vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, VertexAlg/VertexBasic/VertexOperator.lean, Apache-2.0. These are supplier attribution records from the allowed sealed Scribe generation sources; no supplier source is copied or rebuilt here, and no review result is inherited.

This unit supplies the actual lattice carrier with a positive finite energy grading and identifies it with the actual Sugawara L_0 eigenspaces under the explicit inverse pair. It does not construct a PCT involution, Hermitian form, analytic Hilbert completion, twisted vertex algebra, Monster realization, fusion category, anomaly, string theory or AdS/CFT. The complete supplier Virasoro theorem is a separate result and is not replaced by these modules.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.actualL0_basis`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.actualL0_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.actualL0_eigen_iff_grade`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.actualL0_eigenspace_eq_grade`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.actual_mode_grade`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.carrierCoeffEquiv_basis`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.chargeEnergy_complex_half`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.complex_inverse_exists`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualLZeroGrading.positive_actual_mode_grade`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalEnergy](LatticeActualConformalEnergy.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeEnergyGrading](LatticeEnergyGrading.md)
