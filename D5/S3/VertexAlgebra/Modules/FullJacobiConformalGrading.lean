/- GID: D5/S3/VertexAlgebra/Modules/FullJacobiConformalGrading
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Modules/FullJacobiConformalGrading
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual conformal weight shifts and conditional Fock reconstruction. -//- Delivery scope and attribution: all 24 original authored declarations / 64 native objects are preserved from accepted source SHA256 e837ca913b12d23efbc388e8cca93df434fc5d55ed7c492b1d19af051b8d0694. proof_shape: content for actual omega-current products, the p=1 module commutator, the all-integer actual-L0 current commutator, generalized-eigenspace transport with unchanged Nat-infinity Jordan order, lower-bound nilpotence, and the conditional Weyl/Fock/Taylor bridge; local instances and private power helpers are consumed on these proof paths. admission_basis: escape-witness. utility: none: these are symbolic constructions and proofs for arbitrary lattice data and an independent-universe arbitrary complex module, including rank zero and zero M; no bounded enumeration, checker, numerical reduction or certified instance is delivered. LowerBoundedConformalSpectrum J H is SEPARATE additional data: a real lower bound and finite algebraic decomposition into actual generalized L0 eigenspaces. It is required for nilpotence, normalizedWeylData, conformalFockEquiv and Taylor, and is not derived here for every weak module. No diagonalizability, finite-dimensionality or oscillator-basis assumption replaces it. Positive-current vacuum leaves zero modes unrestricted. Both inverse-Gram equations remain exactly where stated. The equivalence is a complex vector-space equivalence with the specified negative-current monomial action and reuses the generic Fock inverse/Taylor proof. Original source and supplier attribution are retained below; no literature-priority claim is made. The generated Blueprint comes from make emit; no separate experimental artifact is specified. The four-slot source-bound audit is unfinished for all 16 public theorems: exact source reconstruction, full Law equivalence, rejected intervention, sensitivity and actual observational dependence remain unproved. Details: https://github.com/the-omega-institute/trureturing/issues/29487. No Contract registration, client enrollment or declared_validated status is claimed; the uncompiled sourceScope stub is not retained. The full original mathematical goal remains active and incomplete. -/


import D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport
import D5.S3.VertexAlgebra.LatticeActualConformalWard
import D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-
Native kernel evidence is recorded separately; this source is not an official receipt.

The full mixed-Jacobi module, current normalization and finite activity are
consumed from FullJacobiCurrentTransport after native API/proof repairs.
Original candidate SHA-256
890e2c8ec32289d944299882c7e59cfced0b3bdeb810e27d5aaf5ab7841b61ef.
That supplier retains Scott Carnahan's Apache 2.0 attribution, the
Matsuo--Nagatomo reference and Kalle Kytölä's actual-current attribution.
The actual omega and Sugawara suppliers retain Bakalov--Kac math/0402315v1,
section 4.1, (4.12)--(4.16), DOI 10.1142/9789812702562_0001, and the
VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4.
The finite p=1 commutator extraction follows the imported actual source
calculus; here its field and its evaluation are genuinely on arbitrary M.

The Taylor/Fock proof is NOT repeated. We consume WeylData and its actual
fockEquiv, fockMap_monomial and taylor_reconstruction from the completed
AlgebraicHeisenbergFock after native API/proof repairs. Original candidate SHA-256
997b7b982da5609c547043695037e16cd3c96ce1d70007e653437e6911d91bd9.
The classical normal-ordered Taylor formula and factorial convention are
attributed there. Generalized eigenspaces use mathlib's Eigenspace.Basic
(Alexander Bentkamp, Apache 2.0); they are not newly postulated subspaces.

Only LowerBoundedConformalSpectrum is extra module-class data. It states
finite algebraic decomposition into ACTUAL L0 generalized eigenspaces and
a real lower bound for their nonzero vectors. It says nothing about current
degrees, nilpotence, oscillator bases, zero modes or Fock factors. Complex
weights may have arbitrary real and imaginary offsets. Neither finite
dimensionality of weight spaces nor semisimplicity of L0 is required.
No such spectral hypothesis is claimed for all weak Jacobi modules.
Zero M and rank zero are allowed throughout, with empty sums/intersections.
The resulting equivalence is of complex vector spaces with its stated
oscillator monomial action, not a charged-VOA module/category equivalence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSugawaraConformal
open LatticeSugawaraCurrents LatticeFiniteNegativeGeneration FullJacobiCurrentTransport
open D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator TensorProduct

noncomputable section
universe u

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The actual quadratic conformal state's zero product, on the original
carrier and the original creation-defined current. Both inverse orientations
are precisely those of the original Sugawara translation theorem. -/
theorem source_omega_zero_current (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i : Fin D.rank) :
    sourceProduct D (LatticeActualConformalState.omega D H) 0 (currentState D i) =
      translation D (currentState D i) := by
  rw [sourceProduct, LatticeActualConformalWard.omega_ncoeff,
    show (0 : ℤ) - 1 = -1 by omega,
    sugawaraMode_minus_one_eq_translation D H hHG hGH]

/-- Source creativity kills L0 on the actual vacuum. The actual Sugawara
commutator at (0,-1) then computes omega_1 current without assuming a
current eigenvalue, an inverse symmetry axiom, or a source grading record. -/
theorem source_omega_one_current (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i : Fin D.rank) :
    sourceProduct D (LatticeActualConformalState.omega D H) 1 (currentState D i) =
      currentState D i := by
  have hv : sugawaraMode D H 0 (vacuum D) = 0 := by
    rw [← LatticeActualConformalState.omega_modes D H 0]
    exact stateField_creativity D (LatticeActualConformalState.omega D H) 1
      (by norm_num)
  have hc := congrArg (fun A : Module.End ℂ (Carrier D) => A (vacuum D))
    (sugawaraMode_current_commutator D H hHG hGH i 0 (-1))
  have hs : neutralMode D i (-1) (vacuum D) = currentState D i := by
    rw [currentState, neutralField_ncoeff]
  have he : sugawaraMode D H 0 (currentState D i) = currentState D i := by
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      hv, map_zero, sub_zero, zero_add, Int.cast_neg, Int.cast_one,
      neg_neg, one_smul, hs] using hc
  rw [sourceProduct, LatticeActualConformalWard.omega_ncoeff, sub_self]
  exact he

/-- The p=1 specialization on arbitrary M. Binomial support, rather than
any premise about higher omega products, leaves only source products 0,1. -/
theorem module_one_mode_commutator (J : FullJacobiLatticeModule D M)
    (a b : Carrier D) (n : ℤ) :
    mode J a 1 * mode J b n - mode J b n * mode J a 1 =
      mode J (sourceProduct D a 0 b) (n + 1) +
        mode J (sourceProduct D a 1 b) n := by
  classical
  rw [module_mode_commutator]
  have finite : (∑ᶠ j : ℕ, commutatorTerm J a b 1 n j) =
      ∑ j ∈ Finset.range 2, commutatorTerm J a b 1 n j := by
    apply finsum_eq_sum_of_support_subset
    intro j member
    by_contra outside
    have hj : 1 < j := by
      have hn : ¬ j < 2 := by simpa only [Finset.mem_coe, Finset.mem_range] using outside
      omega
    have vanish : (1 : ℕ).choose j = 0 :=
      Nat.choose_eq_zero_of_lt hj
    have choose : Ring.choose (1 : ℤ) j = 0 := by
      change Ring.choose ((1 : ℕ) : ℤ) j = 0
      simp only [Ring.choose_natCast, vanish, Nat.cast_zero]
    exact member (by simp [commutatorTerm, integerBinomial, choose])
  rw [finite]
  simp [Finset.sum_range_succ, commutatorTerm, integerBinomial,
    Ring.choose_one_right, add_comm n 1]

/-- ACTUAL module L0 = Y_M(actual omega)_1, not a chosen degree operator. -/
abbrev L0 (J : FullJacobiLatticeModule D M)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Module.End ℂ M :=
  mode J (LatticeActualConformalState.omega D H) 1

/-- Full mixed Jacobi, the two proved source products and derived module
translation give the all-INTEGER conformal-current law on arbitrary M. -/
theorem L0_current_commutator (J : FullJacobiLatticeModule D M)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i : Fin D.rank) (n : ℤ) :
    L0 J H * current J i n - current J i n * L0 J H =
      -(n : ℂ) • current J i n := by
  change mode J (LatticeActualConformalState.omega D H) 1 * mode J (currentState D i) n -
    mode J (currentState D i) n * mode J (LatticeActualConformalState.omega D H) 1 =
      -(n : ℂ) • mode J (currentState D i) n
  rw [module_one_mode_commutator, source_omega_zero_current D H hHG hGH,
    source_omega_one_current D H hHG hGH, module_translation_modes,
    show n + 1 - 1 = n by omega]
  simp only [Int.cast_add, Int.cast_one]
  calc
    -((n : ℂ) + 1) • mode J (currentState D i) n + mode J (currentState D i) n =
        (-((n : ℂ) + 1) + 1) • mode J (currentState D i) n := by
      rw [add_smul, one_smul]
    _ = -(n : ℂ) • mode J (currentState D i) n := by congr 1; ring

private theorem shifted_intertwiner (L A : Module.End ℂ M) (c z : ℂ)
    (h : L * A - A * L = -c • A) :
    (L - (z - c) • 1) * A = A * (L - z • 1) := by
  calc
    (L - (z - c) • 1) * A = L * A - (z - c) • A := by
      rw [sub_mul, smul_mul_assoc, one_mul]
    _ = (L * A - A * L) + A * L - z • A + c • A := by
      rw [sub_smul]
      abel
    _ = A * L - z • A := by rw [h, neg_smul]; abel
    _ = A * (L - z • 1) := by rw [mul_sub, mul_smul_comm, mul_one]

private theorem intertwining_powers (B C A : Module.End ℂ M)
    (h : B * A = A * C) (k : ℕ) : B ^ k * A = A * C ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        B ^ (k + 1) * A = B ^ k * (B * A) := by rw [pow_succ, mul_assoc]
        _ = B ^ k * (A * C) := by rw [h]
        _ = (B ^ k * A) * C := by rw [mul_assoc]
        _ = (A * C ^ k) * C := by rw [ih]
        _ = A * C ^ (k + 1) := by rw [pow_succ, mul_assoc]

/-- A proved commutator transports every finite Jordan order, and also
the union of all finite orders (k=top). No finite-dimensionality is used. -/
private theorem commutator_genEigenspace_shift (L A : Module.End ℂ M)
    (c z : ℂ) (h : L * A - A * L = -c • A) (k : ℕ∞) (v : M)
    (hv : v ∈ L.genEigenspace z k) :
    A v ∈ L.genEigenspace (z - c) k := by
  obtain ⟨l, hl, hv⟩ := Module.End.mem_genEigenspace.mp hv
  apply Module.End.mem_genEigenspace.mpr
  refine ⟨l, hl, ?_⟩
  rw [LinearMap.mem_ker] at hv ⊢
  have hp := congrArg (fun T : Module.End ℂ M => T v)
    (intertwining_powers (L - (z - c) • 1) (L - z • 1) A
      (shifted_intertwiner L A c z h) l)
  simpa only [Module.End.mul_apply, hv, map_zero] using hp

/-- Genuine generalized-weight shift for every integer current mode,
preserving the Jordan-order bound and arbitrary complex spectral offsets. -/
theorem current_genEigenspace_shift (J : FullJacobiLatticeModule D M)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i : Fin D.rank) (n : ℤ) (z : ℂ) (k : ℕ∞) (v : M)
    (hv : v ∈ (L0 J H).genEigenspace z k) :
    current J i n v ∈ (L0 J H).genEigenspace (z - (n : ℂ)) k :=
  commutator_genEigenspace_shift (L0 J H) (current J i n) (n : ℂ) z
    (L0_current_commutator J H hHG hGH i n) k v hv

/-- Ordinary eigenspaces are the order-one specialization, still indexed
by all complex numbers rather than an imposed integer spectrum. -/
theorem current_eigenspace_shift (J : FullJacobiLatticeModule D M)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i : Fin D.rank) (n : ℤ) (z : ℂ) (v : M)
    (hv : v ∈ (L0 J H).eigenspace z) :
    current J i n v ∈ (L0 J H).eigenspace (z - (n : ℂ)) :=
  current_genEigenspace_shift J H hHG hGH i n z 1 v hv

/-- Linear normalization preserves the genuine shifted generalized
eigenspace because that target is a submodule, not a chosen oscillator grade. -/
theorem annihilation_genEigenspace_shift (J : FullJacobiLatticeModule D M)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i : Fin D.rank) (r : ℕ) (z : ℂ) (k : ℕ∞) (v : M)
    (hv : v ∈ (L0 J H).genEigenspace z k) :
    annihilation J H i r v ∈ (L0 J H).genEigenspace (z - (r + 1 : ℂ)) k := by
  have hc (j : Fin D.rank) : current J j ((r : ℤ) + 1) v ∈
      (L0 J H).genEigenspace (z - (r + 1 : ℂ)) k := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using
      current_genEigenspace_shift J H hHG hGH j ((r : ℤ) + 1) z k v hv
  simp only [annihilation, rowMode, LinearMap.smul_apply, LinearMap.sum_apply]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (hc j)

/-- Every power lowers the actual complex weight by its positive integral
frequency, without increasing the generalized-eigenvector order. -/
theorem annihilation_pow_genEigenspace_shift (J : FullJacobiLatticeModule D M)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i : Fin D.rank) (r : ℕ) (z : ℂ) (k : ℕ∞) (v : M)
    (hv : v ∈ (L0 J H).genEigenspace z k) (q : ℕ) :
    (annihilation J H i r ^ q) v ∈
      (L0 J H).genEigenspace (z - (q : ℂ) * (r + 1 : ℂ)) k := by
  induction q with
  | zero => simpa using hv
  | succ q ih =>
      have hs := annihilation_genEigenspace_shift J H hHG hGH i r
        (z - (q : ℂ) * (r + 1 : ℂ)) k ((annihilation J H i r ^ q) v) ih
      have scalar : z - (q : ℂ) * (r + 1 : ℂ) - (r + 1 : ℂ) =
          z - ((q + 1 : ℕ) : ℂ) * (r + 1 : ℂ) := by push_cast; ring
      rw [scalar] at hs
      simpa only [pow_succ', Module.End.mul_apply] using hs

/-- Independent conformal spectral module-class assumptions. All spaces
are the actual L0 generalized eigenspaces. Finite decomposition is algebraic;
no basis, oscillator factors, current shift, nilpotence or positivity on M
is part of this data. A zero vector need not have a nonzero component. -/
structure LowerBoundedConformalSpectrum (J : FullJacobiLatticeModule D M)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) where
  lowerBound : ℝ
  finite_decomposition : ∀ v : M, ∃ s : Finset ℂ, ∃ w : ℂ → M,
    (∀ z ∈ s, w z ∈ (L0 J H).genEigenspace z ⊤) ∧ (∑ z ∈ s, w z) = v
  lower_bound : ∀ (z : ℂ) (v : M),
    v ∈ (L0 J H).genEigenspace z ⊤ → v ≠ 0 → lowerBound ≤ z.re

/-- Below the real spectral bound the actual generalized eigenspace
contains only zero. This does not assume any annihilator vanishes. -/
theorem generalized_below_eq_zero (J : FullJacobiLatticeModule D M)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (S : LowerBoundedConformalSpectrum J H) (z : ℂ) (v : M)
    (hv : v ∈ (L0 J H).genEigenspace z ⊤) (hz : z.re < S.lowerBound) : v = 0 := by
  by_contra hne
  exact (not_le_of_gt hz) (S.lower_bound z v hv hne)

/-- An explicit real inequality forces the normalized positive-current
power to vanish on a generalized homogeneous vector. -/
theorem annihilation_pow_eq_zero_below (J : FullJacobiLatticeModule D M)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (S : LowerBoundedConformalSpectrum J H)
    (i : Fin D.rank) (r : ℕ) (z : ℂ) (v : M)
    (hv : v ∈ (L0 J H).genEigenspace z ⊤) (q : ℕ)
    (hq : z.re - (q : ℝ) * (r + 1 : ℝ) < S.lowerBound) :
    (annihilation J H i r ^ q) v = 0 := by
  apply generalized_below_eq_zero J H S (z - (q : ℂ) * (r + 1 : ℂ))
  · exact annihilation_pow_genEigenspace_shift J H hHG hGH i r z ⊤ v hv q
  · simpa [Complex.mul_re] using hq

theorem annihilation_nilpotent_on_genEigenspace (J : FullJacobiLatticeModule D M)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (S : LowerBoundedConformalSpectrum J H)
    (i : Fin D.rank) (r : ℕ) (z : ℂ) (v : M)
    (hv : v ∈ (L0 J H).genEigenspace z ⊤) :
    ∃ q : ℕ, (annihilation J H i r ^ q) v = 0 := by
  obtain ⟨q, hq⟩ := exists_nat_gt (z.re - S.lowerBound)
  refine ⟨q, annihilation_pow_eq_zero_below J H hHG hGH S i r z v hv q ?_⟩
  have hr : (1 : ℝ) ≤ (r + 1 : ℝ) := by
    have h : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    linarith
  have hmul : (q : ℝ) ≤ (q : ℝ) * (r + 1 : ℝ) :=
    le_mul_of_one_le_right (Nat.cast_nonneg q) hr
  linarith

/-- Finite actual spectral decomposition upgrades homogeneous nilpotence
to every vector. The zero generalized eigenspace of the annihilator is a
submodule: its finite-sum closure provides a common finite exponent.
There is no uniform exponent assumption and no infinite-sum argument. -/
theorem annihilation_locally_nilpotent (J : FullJacobiLatticeModule D M)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (S : LowerBoundedConformalSpectrum J H)
    (i : Fin D.rank) (r : ℕ) (v : M) :
    ∃ q : ℕ, (annihilation J H i r ^ q) v = 0 := by
  obtain ⟨s, w, hw, hs⟩ := S.finite_decomposition v
  have hm : v ∈ (annihilation J H i r).genEigenspace 0 ⊤ := by
    rw [← hs]
    apply Submodule.sum_mem
    intro z hz
    obtain ⟨q, hq⟩ :=
      annihilation_nilpotent_on_genEigenspace J H hHG hGH S i r z (w z) (hw z hz)
    apply Module.End.mem_genEigenspace_top.mpr
    refine ⟨q, ?_⟩
    simpa only [zero_smul, sub_zero, LinearMap.mem_ker] using hq
  obtain ⟨q, hq⟩ := Module.End.mem_genEigenspace_top.mp hm
  exact ⟨q, by simpa only [zero_smul, sub_zero, LinearMap.mem_ker] using hq⟩

/-- Every WeylData hypothesis is now derived from full Jacobi, actual
omega, the independent spectral data, and HG/GH. This definition is
consumed below by the existing generic Taylor tensor reconstruction. -/
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

/-- The ORIGINAL strictly positive current vacuum; the zero modes are
unrestricted. The natural indexing enumerates every positive integer. -/
def positiveVacuum (J : FullJacobiLatticeModule D M) : Submodule ℂ M :=
  ⨅ p : Fin D.rank × ℕ, LinearMap.ker (current J p.1 ((p.2 : ℤ) + 1))

theorem mem_positiveVacuum (J : FullJacobiLatticeModule D M) (v : M) :
    v ∈ positiveVacuum J ↔
      ∀ (i : Fin D.rank) (n : ℤ), 0 < n → current J i n v = 0 := by
  simp only [positiveVacuum, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hv i n hn
    let r : ℕ := (n - 1).toNat
    have index : n = (r : ℤ) + 1 := by dsimp [r]; omega
    rw [index]
    exact hv (i, r)
  · intro hv p
    exact hv p.1 ((p.2 : ℤ) + 1) (by omega)

/-- GH, with its original orientation, identifies the generic Taylor
vacuum with the actual positive-current kernel; no vacuum identification
or oscillator decomposition is assumed. -/
theorem normalizedWeylData_vacuum_eq (J : FullJacobiLatticeModule D M)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (S : LowerBoundedConformalSpectrum J H) :
    (normalizedWeylData J H hHG hGH S).vacuum = positiveVacuum J := by
  ext v
  rw [WeylData.mem_vacuum, mem_positiveVacuum]
  change (∀ p : Fin D.rank × ℕ, annihilation J H p.1 p.2 v = 0) ↔ _
  constructor
  · intro hv
    exact (normalized_vacuum_iff J H hGH v).mp (fun i r => hv (i, r))
  · intro hv p
    exact (normalized_vacuum_iff J H hGH v).mpr hv p.1 p.2

/-- Concrete consumer of the existing arbitrary-index Fock proof, on the
ACTUAL original positive-current vacuum and the arbitrary carrier M.
This is a vector-space equivalence, not a full charged-module classification. -/
def conformalFockEquiv (J : FullJacobiLatticeModule D M)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (S : LowerBoundedConformalSpectrum J H) :
    (MvPolynomial (Fin D.rank × ℕ) ℂ ⊗[ℂ] positiveVacuum J) ≃ₗ[ℂ] M :=
  (LinearEquiv.lTensor (MvPolynomial (Fin D.rank × ℕ) ℂ)
    (LinearEquiv.ofEq (positiveVacuum J) (normalizedWeylData J H hHG hGH S).vacuum
      (normalizedWeylData_vacuum_eq J H hHG hGH S).symm)).trans
        (normalizedWeylData J H hHG hGH S).fockEquiv

/-- Its forward map acts by the ORIGINAL negative current modes on a
polynomial monomial and includes the original positive-current vacuum. -/
theorem conformalFockEquiv_monomial (J : FullJacobiLatticeModule D M)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (S : LowerBoundedConformalSpectrum J H)
    (d : (Fin D.rank × ℕ) →₀ ℕ) (v : positiveVacuum J) :
    conformalFockEquiv J H hHG hGH S (MvPolynomial.monomial d (1 : ℂ) ⊗ₜ[ℂ] v) =
      (normalizedWeylData J H hHG hGH S).creation d (v : M) := by
  let e := LinearEquiv.ofEq (positiveVacuum J) (normalizedWeylData J H hHG hGH S).vacuum
    (normalizedWeylData_vacuum_eq J H hHG hGH S).symm
  change (normalizedWeylData J H hHG hGH S).fockEquiv
    ((e.lTensor (MvPolynomial (Fin D.rank × ℕ) ℂ))
      (MvPolynomial.monomial d (1 : ℂ) ⊗ₜ[ℂ] v)) = _
  rw [LinearEquiv.lTensor_tmul]
  change (normalizedWeylData J H hHG hGH S).fockMap
    (MvPolynomial.monomial d (1 : ℂ) ⊗ₜ[ℂ] e v) = _
  exact (normalizedWeylData J H hHG hGH S).fockMap_monomial d (e v)

/-- The actual finite normal-ordered Taylor reconstruction, reusing the
generic proved box and factorial formula without another Fock proof. -/
theorem conformal_taylor_reconstruction (J : FullJacobiLatticeModule D M)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (S : LowerBoundedConformalSpectrum J H) (v : M) :
    let W := normalizedWeylData J H hHG hGH S
    (∑ d ∈ Finset.Iic (W.jointCutoff v), (WeylData.factorial d : ℂ)⁻¹ •
      W.creation d (W.vacuumProjection (W.derivative d v))) = v := by
  exact (normalizedWeylData J H hHG hGH S).taylor_reconstruction v

end
end D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading
