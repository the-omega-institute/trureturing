# Actual Finite Grades, Vacuum and Internal Direct Sum

## Abstract

Exact actual coefficient grades have full fiber bases and finite nonhomogeneous projections.

D is ordinary LatticeGeneratingFieldLocality.LatticeData: any natural rank, including zero, with an integral symmetric Gram matrix G and even diagonal. Charge(D)=Fin(rank(D))->Z; Index(D)=Fin(rank(D)) x N; Exponent(D)=Index(D)->_0 N. The actual Carrier(D) is the finite-support charge sum of complex multivariate polynomials in Index(D). A label is (alpha,d), and its actual basis vector is single(alpha,monomial(d,1)). Write q_D(alpha)=B_D(alpha,alpha)/2 in Z, w(d)=sum_x (x.2+1)*d(x), and E_D(alpha,d)=q_D(alpha)+w(d) in Z. Geometric positivity means exactly hD: Matrix.PosDef(G.map(Int.cast:Z->R)); it is supplied only where stated. There is no positive-rank, integral determinant-unit, unimodularity or assumed finite-grade premise.

Every declaration described here is publicly named in D5.S3.VertexAlgebra.LatticePositiveEnergy, including declarations whose source module has a different file name. Definition bindings expose the actual data or constructed equivalences; the substantive completion consists of the proved positivity, finiteness, decomposition and actual-operator theorems.

Basis, coefficient support, projections and the internal direct sum are constructed for every ordinary D, without hD. hD derives finite-dimensionality, and zero-grade vacuum normalization. The entire Carrier(D) is usually infinite-dimensional when rank is positive; finiteness is asserted for each grade.

**Definition 1.1 (Actual carrier coefficient equivalence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.carrierCoeffEquiv`

*Formalization.* `D5/S3/VertexAlgebra/LatticeEnergyGrading.carrierCoeffEquiv` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Carrier(D) is linearly equivalent over C to Label(D)->_0 C. Polynomial monomial-basis coordinates in each finite-support charge sector are uncurried. No positivity or finiteness of grades is required.

**Definition 1.2 (Basis of the entire actual carrier).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.carrierBasis`

*Formalization.* `D5/S3/VertexAlgebra/LatticeEnergyGrading.carrierBasis` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The actual carrier basis is obtained from carrierCoeffEquiv and is indexed by every charge/exponent label.

**Theorem 1.3 (Actual basis vector formula).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.carrierBasis_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeEnergyGrading.carrierBasis_apply` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

carrierBasis(D,(alpha,d))=single(alpha,monomial(d,1)), exactly on the actual carrier.

**Definition 1.4 (Integer coefficient-support grade).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.grade`

*Formalization.* `D5/S3/VertexAlgebra/LatticeEnergyGrading.grade` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

grade(D,n) is the inverse image under actual coefficient coordinates of Finsupp.supported at {a | E_D(a)=n}. It is a C-submodule of Carrier(D), for each n:Z.

**Theorem 1.5 (Exact grade membership for arbitrary states).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.mem_grade_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeEnergyGrading.mem_grade_iff` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

v belongs to grade(D,n) iff for every label a with E_D(a)!=n, coeff(a.2,v(a.1))=0. v is any actual state, including nonhomogeneous finite sums.

**Definition 1.6 (Full fiber coefficient equivalence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeCoeffEquiv`

*Formalization.* `D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeCoeffEquiv` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

grade(D,n) is linearly equivalent over C to EnergyFiber(D,n)->_0 C. This uses the entire fiber and needs neither positivity nor finiteness.

**Definition 1.7 (Basis indexed by the whole energy fiber).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeBasis`

*Formalization.* `D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeBasis` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The basis of grade(D,n) is indexed by EnergyFiber(D,n), with no finite-fiber premise. hD later proves that this basis index type is finite.

**Theorem 1.8 (Grade is the actual energy-basis span).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.grade_eq_span`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeEnergyGrading.grade_eq_span` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

grade(D,n)=span_C(carrierBasis(D) image {a | E_D(a)=n}), unconditionally for every ordinary D.

**Theorem 1.9 (Derived finite-dimensional actual grades).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.grade_finiteDimensional`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeEnergyGrading.grade_finiteDimensional` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Under hD, grade(D,n) is finite-dimensional over C for every integer n. The proof uses the constructed grade basis and the derived finite full fiber; finite-dimensionality is not a hypothesis.

**Theorem 1.10 (Zero grade is exactly the actual vacuum line).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.grade_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeEnergyGrading.grade_zero` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Under hD, grade(D,0)=span_C{vacuum(D)}. The only energy-zero label is (0,0), whose actual basis vector is single(0,1).

**Theorem 1.11 (Actual vacuum is nonzero).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.vacuum_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeEnergyGrading.vacuum_nonzero` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

vacuum(D)!=0 for every ordinary D. This does not require positivity, a conformal inverse, or positive rank.

**Definition 1.12 (Scalar parametrization of zero grade).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.vacuumGradeEquiv`

*Formalization.* `D5/S3/VertexAlgebra/LatticeEnergyGrading.vacuumGradeEquiv` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Under hD, the constructed linear equivalence C ~= grade(D,0) is scalar multiplication of the actual vacuum, transported through grade_zero.

**Theorem 1.13 (Rank-zero label type has one element).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.rank_zero_label`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeEnergyGrading.rank_zero_label` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Assuming only D.rank=0, every label equals (0,0). No positivity or inverse-Gram equation is needed.

**Theorem 1.14 (Rank-zero carrier is the vacuum span).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.rank_zero_carrier`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeEnergyGrading.rank_zero_carrier` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Assuming only D.rank=0, span_C{vacuum(D)}=top on the entire actual Carrier(D), by the exact carrier basis.

**Definition 1.15 (Rank-zero actual carrier is one vacuum line).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.rankZeroVacuumEquiv`

*Formalization.* `D5/S3/VertexAlgebra/LatticeEnergyGrading.rankZeroVacuumEquiv` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Assuming only D.rank=0, the actual carrier is linearly equivalent to C by scalar multiplication of vacuum. The general finite-rank theorems above do not reduce to this boundary case.

**Definition 1.16 (Actual coefficient-filter projection).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeProjection`

*Formalization.* `D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeProjection` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

gradeProjection(D,n) is the actual linear endomorphism obtained by keeping just coefficients at energy n and transporting back to Carrier(D).

**Theorem 1.17 (Projection acts on exact coefficients).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeProjection_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeProjection_coeff` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

At label a, the coefficient of gradeProjection(D,n,v) is the original coefficient if E_D(a)=n, and zero otherwise.

**Theorem 1.18 (Projection lands in its actual grade).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeProjection_mem`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeProjection_mem` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

gradeProjection(D,n,v) belongs to grade(D,n) for any integer n and actual v.

**Definition 1.19 (Finite energies of a nonhomogeneous actual state).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.stateEnergies`

*Formalization.* `D5/S3/VertexAlgebra/LatticeEnergyGrading.stateEnergies` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

stateEnergies(D,v) is the finite image under E_D of the support of carrierCoeffEquiv(D,v). No homogeneity or positivity is assumed.

**Theorem 1.20 (Finite reconstruction of every actual state).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.sum_gradeProjections`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeEnergyGrading.sum_gradeProjections` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

sum over n in stateEnergies(D,v) of gradeProjection(D,n,v) equals v. This proves a finite nonhomogeneous decomposition on the actual carrier, without hD.

**Theorem 1.21 (Independence against all other grades).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.grades_independent`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeEnergyGrading.grades_independent` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The family grade(D) is iSup-independent: each grade meets the supremum of all the other grades trivially. This is stronger than only pairwise disjointness.

**Theorem 1.22 (All grades span the actual carrier).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.grades_iSup`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeEnergyGrading.grades_iSup` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The supremum over all integer grades is top, by finite projection reconstruction for arbitrary actual states.

**Theorem 1.23 (Genuine actual internal direct sum).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.grades_internal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeEnergyGrading.grades_internal` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

DirectSum.IsInternal(grade(D)) holds: the canonical sum of subtype inclusions from the integer-indexed direct sum is bijective. No hD is needed for internality.

**Definition 1.24 (Constructed canonical decomposition equivalence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeEnergyGrading.carrierEnergyDecomposition`

*Formalization.* `D5/S3/VertexAlgebra/LatticeEnergyGrading.carrierEnergyDecomposition` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Carrier(D) ~= direct sum over n:Z of grade(D,n) as C-linear spaces. This equivalence is the inverse of the canonical sum of actual subtype inclusions, using the proved internality.

Bakalov-Kac, Twisted Modules over Lattice Vertex Algebras, arXiv math/0402315v1 (19 February 2004): section 4.1, printed/PDF page 8, equations (4.3)-(4.5), gives the charge/Fock carrier; page 9, Theorem 4.1 and (4.16), gives the dual-basis conformal vector; page 4, Definition 2.2 and (2.23)-(2.24), gives the conformal grading convention. These are construction and convention locators, not proofs of the new coercivity and counting results.

Borcherds, Vertex algebras, Kac-Moody algebras, and the Monster, PNAS 83 (1986), 3068-3071: the author-hosted retypesetting, section 2, printed/PDF page 2, specifies deg(e^alpha)=B(alpha,alpha)/2 and the frequency-weighted oscillator degree. Its SHA256 is 822e39a2ec7bd33ad81193b06b7a66ae89abcec43c4cb7974d4bc513c3fce5b5. It has no equation numbers there; no correspondence to a particular original journal page is asserted.

Dong-Li-Mason, Regularity of rational vertex operator algebras, arXiv q-alg/9508018v1 (24 August 1995), printed/PDF page 3, Definition 2.1, supplies the ordinary-module finite-dimensional eigenspace and lower-truncation convention. Those properties are derived here from hD, rather than assumed. Its regularity theorem is not proved by this unit.

Lean 4.33.0 and the declared Mathlib pin db584cd6d46c92f209a44c0f1c829460d327499d supply the actual imported finite-support, basis, compactness and matrix APIs. Mathlib adaptations retain Apache-2.0 and the original authorship.

This unit supplies the actual lattice carrier with a positive finite energy grading and identifies it with the actual Sugawara L_0 eigenspaces under the explicit inverse pair. It does not construct a PCT involution, Hermitian form, analytic Hilbert completion, twisted vertex algebra, Monster realization, fusion category, anomaly, string theory or AdS/CFT. The complete supplier Virasoro theorem is a separate result and is not replaced by these modules.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.carrierBasis`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.carrierBasis_apply`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.carrierCoeffEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.carrierEnergyDecomposition`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.grade`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeBasis`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeCoeffEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeProjection`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeProjection_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeProjection_mem`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.grade_eq_span`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.grade_finiteDimensional`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.grade_zero`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.grades_iSup`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.grades_independent`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.grades_internal`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.mem_grade_iff`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.rankZeroVacuumEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.rank_zero_carrier`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.rank_zero_label`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.stateEnergies`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.sum_gradeProjections`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.vacuumGradeEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeEnergyGrading.vacuum_nonzero`
- Dependency: [D5/S3/VertexAlgebra/LatticeAllStateField](LatticeAllStateField.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeChargeCoercivity](LatticeChargeCoercivity.md)
