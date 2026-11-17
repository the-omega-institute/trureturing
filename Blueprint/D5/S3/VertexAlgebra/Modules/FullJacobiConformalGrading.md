# Actual conformal weight shifts and conditional Fock reconstruction

## Abstract

FullJacobiConformalGrading

D is the original LatticeData and M : Type u is any complex AddCommGroup/Module, including zero. J is precisely FullJacobiCurrentTransport.FullJacobiLatticeModule D M with the full source, vacuum field and all-integer mixed Jacobi with three separate finite supports. H is the displayed complex inverse-Gram matrix; the HG and GH equations appear exactly where stated. Actual L0 is mode J (LatticeActualConformalState.omega D H) 1. Generalized shift statements range over arbitrary complex z and k : Nat-infinity, preserving finite Jordan order and its union. Nilpotence, normalizedWeylData, conformalFockEquiv and the Taylor formula additionally require the SEPARATE LowerBoundedConformalSpectrum J H record with its real lower bound and finite actual generalized-spectrum decomposition. This data is not derived for all weak modules here. Rank zero and zero M are allowed. The positive-current vacuum leaves zero modes unrestricted. The equivalence is a complex vector-space equivalence with the stated actual negative-current monomial action.

Actual source omega products are proved using the imported Sugawara/omega suppliers. The p=1 module commutator plus derived module translation gives the all-integer actual-L0 current commutator. Its shifted intertwiner transports powers of L0-z, so generalized eigenspaces shift with unchanged Jordan bound. A positive-frequency power lowers the real spectral part until the separately supplied lower bound forces zero. The separately supplied finite generalized decomposition promotes that homogeneous statement to local nilpotence for every vector via the annihilator generalized zero eigenspace. The adapter already supplies finite activity. These facts build normalizedWeylData and consume the generic Fock inverse proof and Taylor reconstruction; no second Fock proof or oscillator basis hypothesis is introduced.

Each exact source signature below is interpreted in its displayed ORIGINAL Lean variable scope; scope commands introduce names and do not add unused parameters. The sealed native statement-v1 telescope, referenced for every authored entry in transfer-manifest.json, fixes precisely which implicit parameters and instances are actually bound. Definitions and records display their actual constructions/fields. No signature is generalized, specialized, renamed or reproved. Imported suppliers are used only as they occur in the four accepted proofs; their definitions have not been read or repackaged here.

Original universe/open directives (names are resolved in the original source module and the namespace shown for each entry):

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSugawaraConformal

open LatticeSugawaraCurrents LatticeFiniteNegativeGeneration FullJacobiCurrentTransport

open D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock

open StateFieldResidueReconstruction (integerBinomial)

open scoped BigOperators VertexOperator TensorProduct

universe u

**Theorem 1.1 (source_omega_zero_current).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.source_omega_zero_current`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.source_omega_zero_current` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem source_omega_zero_current (D : LatticeData)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    (i : Fin D.rank) :

    sourceProduct D (LatticeActualConformalState.omega D H) 0 (currentState D i) =

      translation D (currentState D i)

Proof mechanism: Use the actual omega coefficient identity and the Sugawara minus-one translation theorem with both inverse-Gram orientations.

**Theorem 1.2 (source_omega_one_current).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.source_omega_one_current`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.source_omega_one_current` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem source_omega_one_current (D : LatticeData)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    (i : Fin D.rank) :

    sourceProduct D (LatticeActualConformalState.omega D H) 1 (currentState D i) =

      currentState D i

Proof mechanism: Source creativity kills actual L0 on vacuum. Evaluate the genuine Sugawara-current commutator at (0,-1) on vacuum and use the creation-defined current to obtain the identity source product.

**Theorem 1.3 (module_one_mode_commutator).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.module_one_mode_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.module_one_mode_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem module_one_mode_commutator (J : FullJacobiLatticeModule D M)

    (a b : Carrier D) (n : ℤ) :

    mode J a 1 * mode J b n - mode J b n * mode J a 1 =

      mode J (sourceProduct D a 0 b) (n + 1) +

        mode J (sourceProduct D a 1 b) n

Proof mechanism: Specialize the module commutator at p=1. Binomial support removes every index above one, leaving the two actual source products.

D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading.L0

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted abbrev:

abbrev L0 (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Module.End ℂ M :=

  mode J (LatticeActualConformalState.omega D H) 1

Construction and use: Use Y_M(actual omega D H)_1 itself, not a selected grading endomorphism.

**Theorem 1.4 (L0_current_commutator).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.L0_current_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.L0_current_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem L0_current_commutator (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    (i : Fin D.rank) (n : ℤ) :

    L0 J H * current J i n - current J i n * L0 J H =

      -(n : ℂ) • current J i n

Proof mechanism: Insert the two proved omega-current source products in module_one_mode_commutator; the derived module translation law combines them into minus n times the actual current for every integer n.

**Theorem 1.5 (current_genEigenspace_shift).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.current_genEigenspace_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.current_genEigenspace_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem current_genEigenspace_shift (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    (i : Fin D.rank) (n : ℤ) (z : ℂ) (k : ℕ∞) (v : M)

    (hv : v ∈ (L0 J H).genEigenspace z k) :

    current J i n v ∈ (L0 J H).genEigenspace (z - (n : ℂ)) k

Proof mechanism: The proved commutator gives (L0-(z-n))*current=current*(L0-z). Induct that intertwining through powers and apply the actual kernel characterization of genEigenspace at every finite order and their union.

**Theorem 1.6 (current_eigenspace_shift).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.current_eigenspace_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.current_eigenspace_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem current_eigenspace_shift (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    (i : Fin D.rank) (n : ℤ) (z : ℂ) (v : M)

    (hv : v ∈ (L0 J H).eigenspace z) :

    current J i n v ∈ (L0 J H).eigenspace (z - (n : ℂ))

Proof mechanism: Specialize current_genEigenspace_shift to generalized order one.

**Theorem 1.7 (annihilation_genEigenspace_shift).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.annihilation_genEigenspace_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.annihilation_genEigenspace_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem annihilation_genEigenspace_shift (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    (i : Fin D.rank) (r : ℕ) (z : ℂ) (k : ℕ∞) (v : M)

    (hv : v ∈ (L0 J H).genEigenspace z k) :

    annihilation J H i r v ∈ (L0 J H).genEigenspace (z - (r + 1 : ℂ)) k

Proof mechanism: Each constituent positive current lands in the same shifted generalized eigenspace; that submodule is closed under the actual H-row sum and reciprocal-frequency scaling.

**Theorem 1.8 (annihilation_pow_genEigenspace_shift).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.annihilation_pow_genEigenspace_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.annihilation_pow_genEigenspace_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem annihilation_pow_genEigenspace_shift (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    (i : Fin D.rank) (r : ℕ) (z : ℂ) (k : ℕ∞) (v : M)

    (hv : v ∈ (L0 J H).genEigenspace z k) (q : ℕ) :

    (annihilation J H i r ^ q) v ∈

      (L0 J H).genEigenspace (z - (q : ℂ) * (r + 1 : ℂ)) k

Proof mechanism: Induct on q using annihilation_genEigenspace_shift, accumulating q times the positive frequency without increasing the Jordan-order bound.

D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading.LowerBoundedConformalSpectrum

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted structure:

structure LowerBoundedConformalSpectrum (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) where

  lowerBound : ℝ

  finite_decomposition : ∀ v : M, ∃ s : Finset ℂ, ∃ w : ℂ → M,

    (∀ z ∈ s, w z ∈ (L0 J H).genEigenspace z ⊤) ∧ (∑ z ∈ s, w z) = v

  lower_bound : ∀ (z : ℂ) (v : M),

    v ∈ (L0 J H).genEigenspace z ⊤ → v ≠ 0 → lowerBound ≤ z.re

Construction and use: Assume separately a real lower bound for nonzero actual L0 generalized eigenvectors and finite algebraic decomposition of every vector into actual generalized eigenspaces. There is no integral-spectrum, semisimplicity, finite-dimensionality, nilpotence, basis or Fock premise.

**Theorem 1.9 (generalized_below_eq_zero).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.generalized_below_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.generalized_below_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem generalized_below_eq_zero (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (S : LowerBoundedConformalSpectrum J H) (z : ℂ) (v : M)

    (hv : v ∈ (L0 J H).genEigenspace z ⊤) (hz : z.re < S.lowerBound) : v = 0

Proof mechanism: A nonzero vector in an actual generalized eigenspace below the real lower bound contradicts S.lower_bound.

**Theorem 1.10 (annihilation_pow_eq_zero_below).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.annihilation_pow_eq_zero_below`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.annihilation_pow_eq_zero_below` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem annihilation_pow_eq_zero_below (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    (S : LowerBoundedConformalSpectrum J H)

    (i : Fin D.rank) (r : ℕ) (z : ℂ) (v : M)

    (hv : v ∈ (L0 J H).genEigenspace z ⊤) (q : ℕ)

    (hq : z.re - (q : ℝ) * (r + 1 : ℝ) < S.lowerBound) :

    (annihilation J H i r ^ q) v = 0

Proof mechanism: The proved power shift places the output below the real bound; generalized_below_eq_zero then kills it using the explicit displayed inequality.

**Theorem 1.11 (annihilation_nilpotent_on_genEigenspace).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.annihilation_nilpotent_on_genEigenspace`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.annihilation_nilpotent_on_genEigenspace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem annihilation_nilpotent_on_genEigenspace (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    (S : LowerBoundedConformalSpectrum J H)

    (i : Fin D.rank) (r : ℕ) (z : ℂ) (v : M)

    (hv : v ∈ (L0 J H).genEigenspace z ⊤) :

    ∃ q : ℕ, (annihilation J H i r ^ q) v = 0

Proof mechanism: Choose a natural q larger than the real distance above the bound; the frequency r+1 is at least one, so annihilation_pow_eq_zero_below applies.

**Theorem 1.12 (annihilation_locally_nilpotent).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.annihilation_locally_nilpotent`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.annihilation_locally_nilpotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem annihilation_locally_nilpotent (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    (S : LowerBoundedConformalSpectrum J H)

    (i : Fin D.rank) (r : ℕ) (v : M) :

    ∃ q : ℕ, (annihilation J H i r ^ q) v = 0

Proof mechanism: Use S.finite_decomposition. Every component lies in the annihilator's generalized zero eigenspace by homogeneous nilpotence; finite-sum closure gives a common finite exponent for the arbitrary original vector.

D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading.normalizedWeylData

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted def:

def normalizedWeylData (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    (S : LowerBoundedConformalSpectrum J H) : WeylData ℂ (Fin D.rank × ℕ) M where

  X p := creation J p.1 p.2

  D p := annihilation J H p.1 p.2

  xx p q := normalized_XX J p.1 q.1 p.2 q.2

  dd p q := normalized_DD J H p.1 q.1 p.2 q.2

  dx p q v := by

    have h := congrArg (fun T : Module.End ℂ M => T v)

      (normalized_DX J H hHG p.1 q.1 p.2 q.2)

    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,

      Module.End.one_apply] at h

    have delta : (if p.2 = q.2 then (if p.1 = q.1 then (1 : ℂ) else 0) else 0) • v =

        if p = q then v else 0 := by

      by_cases hi : p.1 = q.1 <;> by_cases hr : p.2 = q.2 <;>

        simp [Prod.ext_iff, hi, hr]

    rw [delta] at h

    by_cases hpq : p = q <;>

      simpa [hpq] using (sub_eq_iff_eq_add'.mp h)

  nilpotent p v := annihilation_locally_nilpotent J H hHG hGH S p.1 p.2 v

  active_finite v := finite_active_support J H v

Construction and use: Combine the adapter's derived normalized XX, DD and HG-DX, its truncation-derived finite activity and the S-dependent local nilpotence into generic WeylData.

D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading.positiveVacuum

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted def:

def positiveVacuum (J : FullJacobiLatticeModule D M) : Submodule ℂ M :=

  ⨅ p : Fin D.rank × ℕ, LinearMap.ker (current J p.1 ((p.2 : ℤ) + 1))

Construction and use: Intersect the actual strictly positive current kernels indexed by Fin D.rank times Nat; leave current zero modes unrestricted.

**Theorem 1.13 (mem_positiveVacuum).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.mem_positiveVacuum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.mem_positiveVacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem mem_positiveVacuum (J : FullJacobiLatticeModule D M) (v : M) :

    v ∈ positiveVacuum J ↔

      ∀ (i : Fin D.rank) (n : ℤ), 0 < n → current J i n v = 0

Proof mechanism: Identify each positive integer n uniquely with r+1 using r=(n-1).toNat; unfold the kernel intersection.

**Theorem 1.14 (normalizedWeylData_vacuum_eq).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.normalizedWeylData_vacuum_eq`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.normalizedWeylData_vacuum_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem normalizedWeylData_vacuum_eq (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    (S : LowerBoundedConformalSpectrum J H) :

    (normalizedWeylData J H hHG hGH S).vacuum = positiveVacuum J

Proof mechanism: Unfold the generic vacuum and the actual positive-current kernel, then use the adapter's GH-oriented normalized_vacuum_iff.

D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading.conformalFockEquiv

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted def:

def conformalFockEquiv (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    (S : LowerBoundedConformalSpectrum J H) :

    (MvPolynomial (Fin D.rank × ℕ) ℂ ⊗[ℂ] positiveVacuum J) ≃ₗ[ℂ] M :=

  (LinearEquiv.lTensor (MvPolynomial (Fin D.rank × ℕ) ℂ)

    (LinearEquiv.ofEq (positiveVacuum J) (normalizedWeylData J H hHG hGH S).vacuum

      (normalizedWeylData_vacuum_eq J H hHG hGH S).symm)).trans

        (normalizedWeylData J H hHG hGH S).fockEquiv

Construction and use: Transport the polynomial tensor along the proved equality of actual positive-current and normalized vacua, and compose with the generic fockEquiv. Both inverse equations and the separate spectrum data S remain explicit.

**Theorem 1.15 (conformalFockEquiv_monomial).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.conformalFockEquiv_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.conformalFockEquiv_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem conformalFockEquiv_monomial (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    (S : LowerBoundedConformalSpectrum J H)

    (d : (Fin D.rank × ℕ) →₀ ℕ) (v : positiveVacuum J) :

    conformalFockEquiv J H hHG hGH S (MvPolynomial.monomial d (1 : ℂ) ⊗ₜ[ℂ] v) =

      (normalizedWeylData J H hHG hGH S).creation d (v : M)

Proof mechanism: Apply lTensor_tmul to the vacuum identification, then generic fockMap_monomial. Thus the forward map acts by the ORIGINAL negative current modes.

**Theorem 1.16 (conformal_taylor_reconstruction).**

Lean statement: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.conformal_taylor_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.conformal_taylor_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original namespace: D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

Original Lean scope:

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

Exact accepted theorem:

theorem conformal_taylor_reconstruction (J : FullJacobiLatticeModule D M)

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    (S : LowerBoundedConformalSpectrum J H) (v : M) :

    let W := normalizedWeylData J H hHG hGH S

    (∑ d ∈ Finset.Iic (W.jointCutoff v), (WeylData.factorial d : ℂ)⁻¹ •

      W.creation d (W.vacuumProjection (W.derivative d v))) = v

Proof mechanism: Apply the already proved generic taylor_reconstruction to normalizedWeylData. The derived simultaneous finite box and reciprocal factorials remain visible in the conclusion.

The exact accepted source SHA256 is e837ca913b12d23efbc388e8cca93df434fc5d55ed7c492b1d19af051b8d0694. This selected module retains 24 original authored declarations/local instances and 64 full native objects. Original comments and supplier attribution remain byte-for-byte in the preserved mathematical suffix. The source derives these bridges from the cited suppliers; no literature-priority claim is made. The Scribe renders the exact signatures as line paragraphs for the current DSL. The source-bound four-slot audit for all 16 public theorems remains unfinished under CLAUDE.md section 3.9: https://github.com/the-omega-institute/trureturing/issues/29487. No registration, enrollment or declared_validated status is claimed; the supplied sourceScope stub is not retained. No unconditional all-weak-module nilpotence, nonzero or generating Top, Top=positive-current vacuum, full charged module classification, category/fusion realization, string theory or AdS/CFT completion follows. The global objective remains active and incomplete.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.L0_current_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.annihilation_genEigenspace_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.annihilation_locally_nilpotent`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.annihilation_nilpotent_on_genEigenspace`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.annihilation_pow_eq_zero_below`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.annihilation_pow_genEigenspace_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.conformalFockEquiv_monomial`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.conformal_taylor_reconstruction`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.current_eigenspace_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.current_genEigenspace_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.generalized_below_eq_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.mem_positiveVacuum`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.module_one_mode_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.normalizedWeylData_vacuum_eq`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.source_omega_one_current`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading.source_omega_zero_current`
- Dependency: [D5/S3/Quantum/Algebra/AlgebraicHeisenbergFock](../../Quantum/Algebra/AlgebraicHeisenbergFock.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalWard](../LatticeActualConformalWard.md)
- Dependency: [D5/S3/VertexAlgebra/Modules/FullJacobiCurrentTransport](FullJacobiCurrentTransport.md)
