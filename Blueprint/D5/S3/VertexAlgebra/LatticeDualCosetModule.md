# Dual-Coset Fock Modules by Invariant Restriction

## Abstract

Dual-coset Fock sectors inside an auxiliary even lattice.

Let D be any finite-rank integral symmetric lattice with even diagonal, including rank zero. Let beta be any integral charge. E has Gram matrix [[G,beta],[beta^T,0]]. It may be singular or indefinite. Oscillators are complex multivariate polynomials indexed by Fin(rank(D)) times N, and V_D is their finite-support direct sum over integral charges. Rho renames old variables into E; its retraction kills the added variables. J_t sends single(n,P) to single((n,t),rho(P)); P_t extracts last charge t and applies that polynomial retraction. P_t J_t is identity. action(a) compresses the actual ambient Y_E(J0(a)) between J1 and P1. Truncation is inherited state by state; product compatibility is proved separately.

Creation series commute with the explicit polynomial rename by the pinned PowerSeries map and substitution laws. Translation polynomials and their coefficient supports transport along the same injective rename. The new acting charge has last coordinate zero, so the added cocycle terms vanish while every original half-diagonal contribution remains. Old current derivatives commute with rename, and derivatives in the added variables vanish. The original minus-one product theorem gives canonical multiplication recursion, which extends both coefficient transports to the entire original state space.

**Theorem 1.1 (All original source products).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetModule.source_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetModule.source_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original state a,b and integer m, J0((Y_D(a))_m b)=(Y_E(J0(a)))_m J0(b). No source-product compatibility is assumed. The auxiliary construction, coefficient transport and canonical polynomial multiplication recursion prove this identity.

**Theorem 1.2 (The original occurrence recipe).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetModule.action_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetModule.action_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integral charge a and every finite oscillator exponent e, action(single(a,monomial(e,1))) is shiftedWord(a,occurrences_D(e)). The recursion uses the original occurrence list. It does not compare independently chosen occurrence lists in the two lattices.

**Theorem 1.3 (Invariant all-state Fock realization).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetModule.module_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetModule.module_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original state a, every module vector v and every integer m, J1((action(a))_m v)=(Y_E(J0(a)))_m J1(v). Thus every mode of every original input preserves this actual sector.

**Theorem 1.4 (Vacuum action).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetModule.module_vacuum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetModule.module_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and beta, action(vacuum_D) is the identity field: its mode -1 is identity and every other integer mode is zero.

**Theorem 1.5 (Input differentiation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetModule.module_input_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetModule.module_input_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original state a and every integer m, (action(T_D(a)))_m=-m (action(a))_(m-1). Only J0 transports the original translation to the ambient translation. Ambient translation is not restricted to sector one.

**Theorem 1.6 (Three supports and literal module Borcherds).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetModule.module_borcherds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetModule.module_borcherds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original a,b, every module vector v and all integers p,q,r, each of moduleLeft, moduleFirst and moduleSecond has finite support on the natural offset i. With B(p,i) the complex cast of Ring.choose(p,i), moduleLeft(i)=B(p,i) action((Y_D(a))_(r+i)b)_(p+q-i)v, moduleFirst(i)=(-1)^i B(r,i) action(a)_(p+r-i)(action(b)_(q+i)v), and moduleSecond(i)=(-1)^i B(r,i) ((-1)^r action(b)_(q+r-i)(action(a)_(p+i)v)). The sum of moduleLeft is the sum of moduleFirst minus moduleSecond, equivalently the literal weighted difference. The exponent r is integral; the exponent i is natural. The original ambient Borcherds theorem supplies three supports, transported separately through the injective J1 before sums are subtracted.

**Theorem 1.7 (Exact physical dual pairing).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetModule.physical_pairing_integral`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetModule.physical_pairing_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every rational vector mu satisfying sum_j G_ij mu_j=beta_i for every i, and every integral a, sum_ij a_i G_ij mu_j equals the rational cast of the integer sum_i a_i beta_i. No integrality of mu or unimodularity is required.

**Theorem 1.8 (Shifted ground coefficients).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetModule.action_ground_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetModule.action_ground_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integral a,n, every oscillator polynomial P and integer m, action(single(a,1))_m single(n,P) equals shiftedRawSingle(1,a,-m-1,n,P). In raw power k the creation coefficient index is k-B_D(a,n)-sum_i a_i beta_i+d, with d ranging over the finite coefficient support of translatedPolynomial_D(a,P). The multiplier is the original epsilon_D(a,n), including its half-diagonal term, and the resulting charge is a+n.

**Theorem 1.9 (Physical meaning of the actual ground action).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetModule.physical_ground_action`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetModule.physical_ground_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every rational mu, integral beta, exact hDual, integral a,n, polynomial P and integer m, both the integral physical-pairing identity and the complete shifted ground coefficient formula hold. The index of each creation coefficient is -m-1-B_D(a,n)-sum_i a_i beta_i+d. Thus the physical dual shift is proved, rather than supplied as a field-isomorphism premise.

**Theorem 1.10 (Literal shifted currents).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetModule.action_current_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetModule.action_current_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every current i, integral charge n, polynomial P and integer m, the source state single(0,X_(i,0)) acts as single(n,shiftedCurrentPolynomial(1,i,n,m)(P)). Negative m multiplies by X_(i,-m-1). Mode zero multiplies by B_D(e_i,n)+beta_i. Positive m is m times sum_j G_ij partial_(j,m-1).

**Theorem 1.11 (Entire all-state normal-product action).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetModule.action_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetModule.action_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite-charge input v, action(v) is the finite sum over n in its charge support and e in the monomial-coordinate support of v(n), of its actual monomial coefficient times shiftedWord(n,occurrences_D(e)). The field action is defined for arbitrary nonhomogeneous inputs.

**Theorem 1.12 (Explicit sector retraction).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetModule.retraction_injection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetModule.retraction_injection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer t and actual module vector v, P_t(J_t(v))=v, with the concrete charge extraction and complementary-variable evaluation defined above.

**Theorem 1.13 (Each actual sector injection is injective).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetModule.injection_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetModule.injection_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer t, the concrete map J_t is injective, including rank zero. This follows from the explicit retraction, without any field compatibility premise.

**Theorem 1.14 (A fractional charge-changing action).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetModule.fractional_dual_action`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetModule.fractional_dual_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For G=[2], mu=1/2 and beta=1, the exact dual equation holds and mu is not integral. The mode zero of the original charge -1 ground state sends the charge zero constant vector to the charge -1 constant vector with coefficient one. This uses the same full all-state action as the general theorem.

The original lattice construction is due to Bakalov-Kac, math/0402315v1, section 4.1, equations (4.12)-(4.16), DOI 10.1142/9789812702562_0001. Original all-state field, locality, residue and Jacobi sources retain their upstream attribution, including Scott Carnahan, vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache-2.0. The new bridge is the explicit invariant realization on the actual original Fock carrier. It is not a claim of global mathematical novelty.

These are ungraded vertex-algebra module statements. The action of the original conformal state, shifted Virasoro and translation operators, exact rational positive energy, attained minimum, finite grades, coherent representative changes, discriminant classification, irreducibility, fusion, anomaly, Monster or Moonshine realization, CFT, string theory and AdS/CFT remain outside these statements. Under positive definiteness, the later energy target is spectrum inclusion in h+N; equality requires positive rank, because rank zero has only energy zero.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetModule.action_current_coefficients`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetModule.action_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetModule.action_ground_coefficients`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetModule.action_monomial`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetModule.fractional_dual_action`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetModule.injection_injective`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetModule.module_borcherds`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetModule.module_input_derivative`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetModule.module_transport`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetModule.module_vacuum`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetModule.physical_ground_action`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetModule.physical_pairing_integral`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetModule.retraction_injection`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetModule.source_transport`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualStateDerivative](LatticeActualStateDerivative.md)
