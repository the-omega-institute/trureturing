/- GID: D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original integral lattice discriminant sectors and inverse theta dissection. -/

import D5.S3.VertexAlgebra.LatticePositiveEnergy
import D5.S3.Fourier.MatrixGaussianTheta
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! # Original even-lattice discriminant theta sectors -/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Matrix
open scoped BigOperators

namespace D5.S3.VertexAlgebra.LatticeDiscriminantTheta
open LatticeGeneratingFieldLocality LatticePositiveEnergy
open D5.S3.Fourier.MatrixGaussian
noncomputable section

def gramReal (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℝ :=
  D.G.map (Int.cast : ℤ → ℝ)

def gramRat (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℚ :=
  D.G.map (Int.cast : ℤ → ℚ)

def gramMap (D : LatticeData) : Charge D →ₗ[ℤ] Charge D := Matrix.toLin' D.G

def gramRange (D : LatticeData) : Submodule ℤ (Charge D) := (gramMap D).range

/-- The actual cokernel of the original integral Gram endomorphism. -/
abbrev Discriminant (D : LatticeData) := Charge D ⧸ gramRange D

def classOf (D : LatticeData) (r : Charge D) : Discriminant D :=
  Submodule.Quotient.mk r

private lemma real_det (D : LatticeData) : (gramReal D).det = (D.G.det : ℝ) := by
  exact (Int.castRingHom ℝ).map_det D.G |>.symm

private lemma rat_det (D : LatticeData) : (gramRat D).det = (D.G.det : ℚ) := by
  exact (Int.castRingHom ℚ).map_det D.G |>.symm

private lemma real_unit (D : LatticeData) (hD : (gramReal D).PosDef) :
    IsUnit (gramReal D).det := isUnit_iff_ne_zero.mpr hD.det_pos.ne'

private lemma rat_unit (D : LatticeData) (hD : (gramReal D).PosDef) :
    IsUnit (gramRat D).det := by
  apply isUnit_iff_ne_zero.mpr
  rw [rat_det]
  exact_mod_cast (show D.G.det ≠ 0 by
    intro h
    have := hD.det_pos
    simp [real_det, h] at this)

private lemma gramMap_injective (D : LatticeData) (hD : (gramReal D).PosDef) :
    Function.Injective (gramMap D) := by
  intro x y h
  have hc : gramReal D *ᵥ (fun i => (x i : ℝ)) =
      gramReal D *ᵥ (fun i => (y i : ℝ)) := by
    funext i
    have hi := congrArg (fun v => (v i : ℝ)) h
    exact ((Int.castRingHom ℝ).map_mulVec D.G x i).symm.trans
      (hi.trans ((Int.castRingHom ℝ).map_mulVec D.G y i))
  have he := (Matrix.mulVec_injective_iff_isUnit.mpr
    ((gramReal D).isUnit_iff_isUnit_det.mpr (real_unit D hD))) hc
  ext i
  exact_mod_cast congrFun he i

private def rangeEquiv (D : LatticeData) (hD : (gramReal D).PosDef) :
    Charge D ≃ₗ[ℤ] gramRange D :=
  LinearEquiv.ofInjective (gramMap D) (gramMap_injective D hD)

instance discriminantFinite (D : LatticeData) [hD : Fact (gramReal D).PosDef] :
    Finite (Discriminant D) :=
  Submodule.finiteQuotientOfFreeOfRankEq (gramRange D) (rangeEquiv D hD.out).symm.finrank_eq

private lemma discriminant_card (D : LatticeData) (hD : (gramReal D).PosDef) :
    Nat.card (Discriminant D) = D.G.det.natAbs := by
  have h := Submodule.natAbs_det_equiv (gramRange D) (rangeEquiv D hD)
  have he : (gramRange D).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap ((rangeEquiv D hD) : Charge D →+ gramRange D) =
      gramMap D := by
    ext x i
    rfl
  rw [he, gramMap, LinearMap.det_toLin'] at h
  exact h.symm

private lemma discriminant_card_real (D : LatticeData) (hD : (gramReal D).PosDef) :
    (Nat.card (Discriminant D) : ℝ) = (gramReal D).det := by
  have hp : 0 ≤ D.G.det := by
    exact_mod_cast (show (0 : ℝ) ≤ (D.G.det : ℝ) by
      rw [← real_det D]
      exact hD.det_pos.le)
  have hn : (D.G.det.natAbs : ℤ) = D.G.det := by
    rw [Int.natCast_natAbs, abs_of_nonneg hp]
  rw [discriminant_card D hD, real_det]
  simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hn

/-- Inversion is performed in the rational scalar extension. -/
def inverseRat (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℚ := (gramRat D)⁻¹

private lemma inverse_cast (D : LatticeData) (hD : (gramReal D).PosDef) :
    (inverseRat D).map (Rat.castHom ℝ) = (gramReal D)⁻¹ := by
  have h := congrArg (fun A : Matrix (Fin D.rank) (Fin D.rank) ℚ =>
    A.map (Rat.castHom ℝ)) (Matrix.mul_nonsing_inv (gramRat D) (rat_unit D hD))
  apply (Matrix.inv_eq_right_inv ?_).symm
  rw [Matrix.map_mul] at h
  simpa [gramReal, gramRat, inverseRat, Matrix.map_map, Function.comp_def] using h

private lemma gramReal_symm (D : LatticeData) : (gramReal D)ᵀ = gramReal D := by
  ext i j
  exact congrArg (Int.cast : ℤ → ℝ) (D.symmetric j i)

private lemma gramRat_symm (D : LatticeData) : (gramRat D)ᵀ = gramRat D := by
  ext i j
  exact congrArg (Int.cast : ℤ → ℚ) (D.symmetric j i)

/-- A representative section; no additive splitting is asserted. -/
def representative (D : LatticeData) (a : Discriminant D) : Charge D := Quotient.out a

private lemma class_representative (D : LatticeData) (a : Discriminant D) :
    classOf D (representative D a) = a := Submodule.Quotient.mk_out a

private lemma class_gram (D : LatticeData) (n : Charge D) :
    classOf D (gramMap D n) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr ⟨n, rfl⟩

private lemma class_add (D : LatticeData) (r s : Charge D) :
    classOf D (r + s) = classOf D r + classOf D s := rfl

private lemma coset_surjective (D : LatticeData) :
    Function.Surjective (fun p : Discriminant D × Charge D =>
      representative D p.1 + gramMap D p.2) := by
  intro k
  have hk : k - representative D (classOf D k) ∈ gramRange D :=
    (Submodule.Quotient.eq _).mp (class_representative D (classOf D k)).symm
  obtain ⟨n, hn⟩ := hk
  refine ⟨(classOf D k, n), ?_⟩
  change representative D (classOf D k) + gramMap D n = k
  change gramMap D n = k - representative D (classOf D k) at hn
  rw [hn]
  abel

private lemma coset_injective (D : LatticeData) (hD : (gramReal D).PosDef) :
    Function.Injective (fun p : Discriminant D × Charge D =>
      representative D p.1 + gramMap D p.2) := by
  rintro ⟨a, m⟩ ⟨b, n⟩ h
  have ha := congrArg (classOf D) h
  simp only [class_add, class_representative, class_gram, add_zero] at ha
  subst b
  exact Prod.ext rfl (gramMap_injective D hD (add_left_cancel h))

/-- Every original integer charge occurs exactly once as `rep a + G n`. -/
def cosetEquiv (D : LatticeData) (hD : (gramReal D).PosDef) :
    Discriminant D × Charge D ≃ Charge D :=
  Equiv.ofBijective (fun p => representative D p.1 + gramMap D p.2)
    ⟨coset_injective D hD, coset_surjective D⟩

private lemma cosetEquiv_apply (D : LatticeData) (hD : (gramReal D).PosDef)
    (p : Discriminant D × Charge D) :
    cosetEquiv D hD p = representative D p.1 + gramMap D p.2 := rfl

def dualVector (D : LatticeData) (r : Charge D) : Fin D.rank → ℚ :=
  inverseRat D *ᵥ (fun i => (r i : ℚ))

private lemma dualVector_add (D : LatticeData) (r s : Charge D) :
    dualVector D (r+s) = dualVector D r + dualVector D s := by
  simp only [dualVector]
  rw [show (fun i => ((r+s) i : ℚ)) = (fun i => (r i : ℚ)) +
    (fun i => (s i : ℚ)) by ext i; simp, mulVec_add]

private lemma dualVector_gram (D : LatticeData) (hD : (gramReal D).PosDef)
    (n : Charge D) : dualVector D (gramMap D n) = (fun i => (n i : ℚ)) := by
  have hc : (fun i => (gramMap D n i : ℚ)) =
      gramRat D *ᵥ (fun i => (n i : ℚ)) := by
    ext i
    exact (Int.castRingHom ℚ).map_mulVec D.G n i
  rw [dualVector, hc, inverseRat, mulVec_mulVec,
    nonsing_inv_mul _ (rat_unit D hD), one_mulVec]

private def integerEmbedding (D : LatticeData) : Charge D →ₗ[ℤ] (Fin D.rank → ℚ) where
  toFun n i := (n i : ℚ)
  map_add' r s := by ext i; simp
  map_smul' k r := by ext i; simp

/-- The standard integral lattice in the original rational coordinate space. -/
def integerLattice (D : LatticeData) : Submodule ℤ (Fin D.rank → ℚ) :=
  (integerEmbedding D).range

/-- The inverse image of the integral lattice under the original rational Gram map. -/
def dualLattice (D : LatticeData) : Submodule ℤ (Fin D.rank → ℚ) :=
  (integerLattice D).comap ((Matrix.toLin' (gramRat D)).restrictScalars ℤ)

private def dualMap (D : LatticeData) (hD : (gramReal D).PosDef) :
    Charge D →ₗ[ℤ] dualLattice D where
  toFun r := ⟨dualVector D r, by
    change gramRat D *ᵥ dualVector D r ∈ integerLattice D
    refine ⟨r, ?_⟩
    simp only [dualVector, inverseRat, mulVec_mulVec,
      mul_nonsing_inv _ (rat_unit D hD), one_mulVec]
    rfl⟩
  map_add' r s := Subtype.ext (dualVector_add D r s)
  map_smul' k r := by
    apply Subtype.ext
    change inverseRat D *ᵥ (fun i => ((k • r) i : ℚ)) = k • dualVector D r
    rw [show (fun i => ((k • r) i : ℚ)) = (k : ℚ) • (fun i => (r i : ℚ)) by
      ext i; simp, mulVec_smul]
    rfl

private lemma dualMap_bijective (D : LatticeData) (hD : (gramReal D).PosDef) :
    Function.Bijective (dualMap D hD) := by
  constructor
  · intro r s h
    have hc := congrArg (fun x : dualLattice D => gramRat D *ᵥ x.1) h
    change gramRat D *ᵥ dualVector D r = gramRat D *ᵥ dualVector D s at hc
    simp only [dualVector, inverseRat, mulVec_mulVec,
      mul_nonsing_inv _ (rat_unit D hD), one_mulVec] at hc
    ext i
    exact_mod_cast congrFun hc i
  · intro x
    obtain ⟨r, hr⟩ := x.2
    refine ⟨r, Subtype.ext ?_⟩
    change (fun i => (r i : ℚ)) = gramRat D *ᵥ x.1 at hr
    change inverseRat D *ᵥ (fun i => (r i : ℚ)) = x.1
    rw [hr, inverseRat, mulVec_mulVec, nonsing_inv_mul _ (rat_unit D hD), one_mulVec]

def dualEquiv (D : LatticeData) (hD : (gramReal D).PosDef) :
    Charge D ≃ₗ[ℤ] dualLattice D := LinearEquiv.ofBijective (dualMap D hD)
      (dualMap_bijective D hD)

private def standardDualEmbedding (D : LatticeData) : Charge D →ₗ[ℤ] dualLattice D where
  toFun n := ⟨integerEmbedding D n, by
    change gramRat D *ᵥ (fun i => (n i : ℚ)) ∈ integerLattice D
    refine ⟨gramMap D n, ?_⟩
    ext i
    exact (Int.castRingHom ℚ).map_mulVec D.G n i⟩
  map_add' r s := by ext i; simp [integerEmbedding]
  map_smul' k r := by ext i; simp [integerEmbedding]

/-- The actual copy of the original integral lattice inside its dual. -/
def standardWithinDual (D : LatticeData) : Submodule ℤ (dualLattice D) :=
  (standardDualEmbedding D).range

private lemma dual_range (D : LatticeData) (hD : (gramReal D).PosDef) :
    (gramRange D).map (dualEquiv D hD).toLinearMap = standardWithinDual D := by
  ext x
  constructor
  · rintro ⟨y, ⟨n, rfl⟩, rfl⟩
    refine ⟨n, Subtype.ext ?_⟩
    exact (dualVector_gram D hD n).symm
  · rintro ⟨n, rfl⟩
    refine ⟨gramMap D n, ⟨n, rfl⟩, Subtype.ext ?_⟩
    exact dualVector_gram D hD n

/-- Inverse Gram coordinates induce `Z^d / G Z^d ≃ L* / L` for the original lattice. -/
def dualQuotientEquiv (D : LatticeData) (hD : (gramReal D).PosDef) :
    Discriminant D ≃ₗ[ℤ] dualLattice D ⧸ standardWithinDual D :=
  Submodule.Quotient.equiv (gramRange D) (standardWithinDual D)
    (dualEquiv D hD) (dual_range D hD)

private lemma dual_intrinsic (D : LatticeData) :
    (gramRat D).toBilin'.dualSubmodule (integerLattice D) = dualLattice D := by
  ext x
  have hs (y : Fin D.rank → ℚ) :
      x ⬝ᵥ gramRat D *ᵥ y = y ⬝ᵥ gramRat D *ᵥ x := by
    simpa only [gramRat_symm] using dotProduct_transpose_mulVec (gramRat D) x y
  constructor
  · intro hx
    have hi (i : Fin D.rank) : ∃ z : ℤ, (z : ℚ) = (gramRat D *ᵥ x) i := by
      have hn : integerEmbedding D (Pi.single i 1) ∈ integerLattice D :=
        ⟨Pi.single i 1, rfl⟩
      have h := hx (integerEmbedding D (Pi.single i 1)) hn
      rw [Matrix.toBilin'_apply', hs] at h
      have he : integerEmbedding D (Pi.single i 1) = Pi.single i (1 : ℚ) := by
        ext j
        simp [integerEmbedding, Pi.single_apply]
      rw [he, single_dotProduct, one_mul, Submodule.mem_one] at h
      exact h
    choose r hr using hi
    exact ⟨r, funext hr⟩
  · rintro ⟨r, hr⟩ y ⟨n, rfl⟩
    change (fun i => (r i : ℚ)) = gramRat D *ᵥ x at hr
    rw [Matrix.toBilin'_apply', hs, ← hr]
    apply Submodule.mem_one.mpr
    refine ⟨n ⬝ᵥ r, ?_⟩
    exact (Int.castRingHom ℚ).map_dotProduct n r

def shift (D : LatticeData) (r : Charge D) : Fin D.rank → ℝ :=
  fun i => (dualVector D r i : ℝ)

private lemma shift_eq (D : LatticeData) (hD : (gramReal D).PosDef) (r : Charge D) :
    shift D r = (gramReal D)⁻¹ *ᵥ (fun i => (r i : ℝ)) := by
  ext i
  have h := (Rat.castHom ℝ).map_mulVec (inverseRat D) (fun j => (r j : ℚ)) i
  rw [inverse_cast D hD] at h
  simpa [shift, dualVector, Function.comp_def] using h

/-- The rational construction realizes the full real dual lattice as well as its exact finite quotient. -/
theorem dual_lattice_realization (D : LatticeData) (hD : (gramReal D).PosDef) :
    (gramRat D).toBilin'.dualSubmodule (integerLattice D) = dualLattice D ∧
    Nat.card (Discriminant D) = D.G.det.natAbs ∧
    (Nat.card (Discriminant D) : ℝ) = (gramReal D).det ∧
    (∀ x : Fin D.rank → ℝ,
      (∀ n : Charge D, ∃ z : ℤ,
        x ⬝ᵥ gramReal D *ᵥ (fun i => (n i : ℝ)) = (z : ℝ)) ↔
      ∃ r : Charge D, shift D r = x) := by
  refine ⟨dual_intrinsic D, discriminant_card D hD, discriminant_card_real D hD, ?_⟩
  intro x
  have hs (y : Fin D.rank → ℝ) :
      x ⬝ᵥ gramReal D *ᵥ y = y ⬝ᵥ gramReal D *ᵥ x := by
    simpa only [gramReal_symm] using dotProduct_transpose_mulVec (gramReal D) x y
  constructor
  · intro hx
    have hi (i : Fin D.rank) : ∃ z : ℤ, (z : ℝ) = (gramReal D *ᵥ x) i := by
      obtain ⟨z, hz⟩ := hx (Pi.single i 1)
      refine ⟨z, ?_⟩
      rw [hs] at hz
      have he : (fun j : Fin D.rank => ((Pi.single i (1 : ℤ) : Charge D) j : ℝ)) =
          (Pi.single i (1 : ℝ) : Fin D.rank → ℝ) := by
        ext j
        simp [Pi.single_apply]
      simpa only [he, single_dotProduct, one_mul] using hz.symm
    choose r hr using hi
    refine ⟨r, ?_⟩
    rw [shift_eq D hD, show (fun i => (r i : ℝ)) = gramReal D *ᵥ x from funext hr,
      mulVec_mulVec, nonsing_inv_mul _ (real_unit D hD), one_mulVec]
  · rintro ⟨r, rfl⟩ n
    refine ⟨n ⬝ᵥ r, ?_⟩
    have hh : gramReal D *ᵥ shift D r = (fun i => (r i : ℝ)) := by
      rw [shift_eq D hD, mulVec_mulVec, mul_nonsing_inv _ (real_unit D hD), one_mulVec]
    rw [← dotProduct_transpose_mulVec, gramReal_symm, hh]
    exact ((Int.castRingHom ℝ).map_dotProduct n r).symm

private lemma cast_gram (D : LatticeData) (n : Charge D) :
    (fun i => (gramMap D n i : ℝ)) = gramReal D *ᵥ (fun i => (n i : ℝ)) := by
  ext i
  exact (Int.castRingHom ℝ).map_mulVec D.G n i

private lemma inverse_quadratic_coset (D : LatticeData) (hD : (gramReal D).PosDef)
    (r n : Charge D) :
    quadratic (gramReal D)⁻¹ (fun i => ((r + gramMap D n) i : ℝ)) =
      quadratic (gramReal D) ((fun i => (n i : ℝ)) + shift D r) := by
  have hc : (fun i => ((r + gramMap D n) i : ℝ)) =
      gramReal D *ᵥ ((fun i => (n i : ℝ)) + shift D r) := by
    rw [mulVec_add, shift_eq D hD, mulVec_mulVec,
      mul_nonsing_inv _ (real_unit D hD), one_mulVec, ← cast_gram]
    ext i
    simp [add_comm]
  rw [hc, quadratic, mulVec_mulVec, nonsing_inv_mul _ (real_unit D hD), one_mulVec,
    dotProduct_comm]
  rfl

/-- The literal shifted countable Gaussian, for an arbitrary integer representative. -/
def representativeTheta (D : LatticeData) (r : Charge D) (τ : ℂ) : ℂ :=
  ∑' n : Charge D, Complex.exp (Real.pi * Complex.I * τ *
    (quadratic (gramReal D) ((fun i => (n i : ℝ)) + shift D r) : ℂ))

def sectorTheta (D : LatticeData) (a : Discriminant D) (τ : ℂ) : ℂ :=
  representativeTheta D (representative D a) τ

/-- Rational values modulo the actual integral subgroup. -/
abbrev QmodZ := AddCircle (1 : ℚ)

private def rationalToRealCircle : ℚ →+ AddCircle (1 : ℝ) where
  toFun x := ((x : ℝ) : AddCircle (1 : ℝ))
  map_zero' := by simp
  map_add' x y := by simp [AddCircle.coe_add]

private def qmodToReal : QmodZ →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ)) rationalToRealCircle (by
    intro x hx
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    change (((n • (1 : ℚ) : ℚ) : ℝ) : AddCircle (1 : ℝ)) = 0
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨n, by simp⟩)

private lemma qmodToReal_injective : Function.Injective qmodToReal := by
  suffices hker : ∀ x, qmodToReal x = 0 → x = 0 by
    intro x y h
    apply sub_eq_zero.mp
    apply hker
    simpa only [map_sub, h, sub_self]
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    intro hx
    change ((x : ℝ) : AddCircle (1 : ℝ)) = 0 at hx
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hx
    apply (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr
    refine ⟨n, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hn ⊢
    exact_mod_cast hn

/-- The faithful unit complex phase on rational values modulo integers. -/
def phase : AddChar QmodZ ℂ :=
  Circle.coeHom.compAddChar (AddCircle.toCircle_addChar.compAddMonoidHom qmodToReal)

private lemma phase_injective : Function.Injective phase :=
  Subtype.coe_injective.comp ((AddCircle.injective_toCircle one_ne_zero).comp
    qmodToReal_injective)

private lemma phase_mk (x : ℚ) :
    phase (x : QmodZ) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  change (AddCircle.toCircle (((x : ℝ) : AddCircle (1 : ℝ))) : ℂ) = _
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 1
  push_cast
  ring

private lemma qmod_integer (z : ℤ) : ((z : ℚ) : QmodZ) = 0 :=
  (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr ⟨z, by simp⟩

private def pairRaw (D : LatticeData) (r s : Charge D) : ℚ :=
  dualVector D r ⬝ᵥ (fun i => (s i : ℚ))

private lemma pairRaw_symm (D : LatticeData) (r s : Charge D) :
    pairRaw D r s = pairRaw D s r := by
  have hi : (inverseRat D)ᵀ = inverseRat D := by
    rw [inverseRat, transpose_nonsing_inv, gramRat_symm]
  simp only [pairRaw, dualVector]
  rw [dotProduct_comm, ← dotProduct_transpose_mulVec, hi, dotProduct_comm]

private lemma pairRaw_add_left (D : LatticeData) (r s t : Charge D) :
    pairRaw D (r+s) t = pairRaw D r t + pairRaw D s t := by
  rw [pairRaw, dualVector_add, add_dotProduct]
  rfl

private lemma pairRaw_add_right (D : LatticeData) (r s t : Charge D) :
    pairRaw D r (s+t) = pairRaw D r s + pairRaw D r t := by
  rw [pairRaw_symm D r, pairRaw_add_left, pairRaw_symm D s, pairRaw_symm D t]

private lemma pairRaw_gram_left (D : LatticeData) (hD : (gramReal D).PosDef)
    (n s : Charge D) : pairRaw D (gramMap D n) s = ((n ⬝ᵥ s : ℤ) : ℚ) := by
  rw [pairRaw, dualVector_gram D hD]
  exact ((Int.castRingHom ℚ).map_dotProduct n s).symm

private lemma pairRaw_gram_right (D : LatticeData) (hD : (gramReal D).PosDef)
    (r n : Charge D) : pairRaw D r (gramMap D n) = ((n ⬝ᵥ r : ℤ) : ℚ) := by
  rw [pairRaw_symm, pairRaw_gram_left D hD]

private lemma pairRaw_mod_left (D : LatticeData) (hD : (gramReal D).PosDef)
    (r s t : Charge D) (h : classOf D r = classOf D s) :
    (pairRaw D r t : QmodZ) = (pairRaw D s t : QmodZ) := by
  obtain ⟨m, hm⟩ := (Submodule.Quotient.eq _).mp h
  have hr : r = s + gramMap D m := by
    change gramMap D m = r-s at hm
    rw [hm]
    abel
  rw [hr, pairRaw_add_left, pairRaw_gram_left D hD, AddCircle.coe_add, qmod_integer,
    add_zero]

/-- The actual discriminant pairing, valued in Q/Z. -/
def pairing (D : LatticeData) (a c : Discriminant D) : QmodZ :=
  (pairRaw D (representative D a) (representative D c) : QmodZ)

private lemma pairing_mk (D : LatticeData) (hD : (gramReal D).PosDef)
    (r s : Charge D) : pairing D (classOf D r) (classOf D s) = (pairRaw D r s : QmodZ) := by
  unfold pairing
  rw [pairRaw_mod_left D hD _ r _ (class_representative D _), pairRaw_symm,
    pairRaw_mod_left D hD _ s _ (class_representative D _), pairRaw_symm]

private lemma pairing_symm (D : LatticeData) (a c : Discriminant D) :
    pairing D a c = pairing D c a := by simp only [pairing, pairRaw_symm]

private lemma pairing_add (D : LatticeData) (hD : (gramReal D).PosDef)
    (a b c : Discriminant D) : pairing D (a+b) c = pairing D a c + pairing D b c := by
  induction a using Submodule.Quotient.induction_on with
  | H r =>
    induction b using Submodule.Quotient.induction_on with
    | H s =>
      induction c using Submodule.Quotient.induction_on with
      | H t =>
        change pairing D (classOf D (r+s)) (classOf D t) =
          pairing D (classOf D r) (classOf D t) + pairing D (classOf D s) (classOf D t)
        simp only [pairing_mk D hD, pairRaw_add_left, AddCircle.coe_add]

private lemma pairing_zero (D : LatticeData) (hD : (gramReal D).PosDef)
    (c : Discriminant D) : pairing D 0 c = 0 := by
  have h := pairing_add D hD 0 0 c
  simp only [zero_add] at h
  have hh := congrArg (fun x => x - pairing D 0 c) h
  simpa using hh.symm

private lemma pairing_nondegenerate (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Discriminant D) (ha : ∀ c, pairing D a c = 0) : a = 0 := by
  induction a using Submodule.Quotient.induction_on with
  | H r =>
    have hint (i : Fin D.rank) : ∃ z : ℤ, (z : ℚ) = dualVector D r i := by
      have h := ha (classOf D (Pi.single i 1))
      change pairing D (classOf D r) (classOf D (Pi.single i 1)) = 0 at h
      rw [pairing_mk D hD] at h
      have hs : pairRaw D r (Pi.single i 1) = dualVector D r i := by
        simp [pairRaw, Pi.single_apply, dotProduct]
      rw [hs, AddCircle.coe_eq_zero_iff] at h
      simpa only [zsmul_eq_mul, mul_one] using h
    choose m hm using hint
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨m, ?_⟩
    have hd : (fun i => (m i : ℚ)) = dualVector D r := funext hm
    have hc : (fun i => (gramMap D m i : ℚ)) = (fun i => (r i : ℚ)) := by
      calc
        _ = gramRat D *ᵥ (fun i => (m i : ℚ)) := by
          ext i
          exact (Int.castRingHom ℚ).map_mulVec D.G m i
        _ = gramRat D *ᵥ dualVector D r := congrArg _ hd
        _ = _ := by rw [dualVector, inverseRat, mulVec_mulVec,
          mul_nonsing_inv _ (rat_unit D hD), one_mulVec]
    ext i
    exact_mod_cast congrFun hc i

private lemma integral_dot_gram (D : LatticeData) (m n : Charge D) :
    m ⬝ᵥ gramMap D n = bilinear D m n := by
  simp [gramMap, Matrix.toLin'_apply, dotProduct, mulVec, bilinear,
    Finset.mul_sum, mul_assoc]

private lemma half_pair_add_gram (D : LatticeData) (hD : (gramReal D).PosDef)
    (r m : Charge D) :
    pairRaw D (r + gramMap D m) (r + gramMap D m) / 2 =
      pairRaw D r r / 2 + ((m ⬝ᵥ r + chargeEnergy D m : ℤ) : ℚ) := by
  simp only [pairRaw_add_left, pairRaw_add_right, pairRaw_gram_left D hD,
    pairRaw_gram_right D hD, dotProduct_add, integral_dot_gram, Int.cast_add]
  have he : (bilinear D m m : ℚ) = 2 * (chargeEnergy D m : ℚ) := by
    exact_mod_cast (two_chargeEnergy D m).symm
  rw [he]
  push_cast
  ring

private lemma half_pair_mod (D : LatticeData) (hD : (gramReal D).PosDef)
    (r s : Charge D) (h : classOf D r = classOf D s) :
    ((pairRaw D r r / 2 : ℚ) : QmodZ) = ((pairRaw D s s / 2 : ℚ) : QmodZ) := by
  obtain ⟨m, hm⟩ := (Submodule.Quotient.eq _).mp h
  have hr : r = s + gramMap D m := by
    change gramMap D m = r-s at hm
    rw [hm]
    abel
  rw [hr, half_pair_add_gram D hD, AddCircle.coe_add, qmod_integer, add_zero]

/-- The original even-lattice half norm modulo integers. -/
def quadraticClass (D : LatticeData) (a : Discriminant D) : QmodZ :=
  ((pairRaw D (representative D a) (representative D a) / 2 : ℚ) : QmodZ)

private lemma quadraticClass_mk (D : LatticeData) (hD : (gramReal D).PosDef)
    (r : Charge D) : quadraticClass D (classOf D r) = ((pairRaw D r r / 2 : ℚ) : QmodZ) :=
  half_pair_mod D hD _ r (class_representative D _)

/-- The original half norm is a quadratic refinement of the nondegenerate Q/Z pairing. -/
theorem discriminant_quadratic (D : LatticeData) (hD : (gramReal D).PosDef) :
    (∀ a c : Discriminant D,
      quadraticClass D (a+c) = quadraticClass D a + quadraticClass D c + pairing D a c) ∧
    (∀ (a : Discriminant D) (k : ℤ), quadraticClass D (k • a) = k^2 • quadraticClass D a) ∧
    (∀ a : Discriminant D, (∀ c, pairing D a c = 0) → a = 0) ∧
    Function.Injective phase := by
  refine ⟨?_, ?_, pairing_nondegenerate D hD, phase_injective⟩
  · intro a c
    induction a using Submodule.Quotient.induction_on with
    | H r =>
      induction c using Submodule.Quotient.induction_on with
      | H s =>
        change quadraticClass D (classOf D (r+s)) = quadraticClass D (classOf D r) +
          quadraticClass D (classOf D s) + pairing D (classOf D r) (classOf D s)
        simp only [quadraticClass_mk D hD, pairing_mk D hD]
        rw [← AddCircle.coe_add, ← AddCircle.coe_add]
        congr 1
        rw [pairRaw_add_left, pairRaw_add_right, pairRaw_add_right, pairRaw_symm D s r]
        ring
  · intro a k
    induction a using Submodule.Quotient.induction_on with
    | H r =>
      change quadraticClass D (classOf D (k • r)) = k^2 • quadraticClass D (classOf D r)
      rw [quadraticClass_mk D hD, quadraticClass_mk D hD, ← AddCircle.coe_zsmul]
      congr 1
      have hv : dualVector D (k • r) = k • dualVector D r :=
        congrArg Subtype.val ((dualMap D hD).map_smul k r)
      have hc : (fun i => ((k • r) i : ℚ)) = k • (fun i => (r i : ℚ)) := by
        ext i
        simp
      rw [pairRaw, hv, hc, smul_dotProduct, dotProduct_smul]
      simp only [zsmul_eq_mul, Int.cast_pow, pairRaw]
      ring

private lemma quadratic_shift_expansion (D : LatticeData) (hD : (gramReal D).PosDef)
    (r n : Charge D) :
    quadratic (gramReal D) ((fun i => (n i : ℝ)) + shift D r) =
      (pairRaw D r r : ℝ) + 2 * ((n ⬝ᵥ r + chargeEnergy D n : ℤ) : ℝ) := by
  have hs : gramReal D *ᵥ shift D r = (fun i => (r i : ℝ)) := by
    rw [shift_eq D hD, mulVec_mulVec, mul_nonsing_inv _ (real_unit D hD), one_mulVec]
  have hb : quadratic (gramReal D) (fun i => (n i : ℝ)) = (bilinear D n n : ℝ) := by
    simp [quadratic, gramReal, bilinear, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hp : shift D r ⬝ᵥ (fun i => (r i : ℝ)) = (pairRaw D r r : ℝ) := by
    exact ((Rat.castHom ℝ).map_dotProduct _ _).symm
  have hn : (fun i => (n i : ℝ)) ⬝ᵥ (fun i => (r i : ℝ)) = ((n ⬝ᵥ r : ℤ) : ℝ) :=
    ((Int.castRingHom ℝ).map_dotProduct n r).symm
  have hc : shift D r ⬝ᵥ gramReal D *ᵥ (fun i => (n i : ℝ)) =
      (fun i => (n i : ℝ)) ⬝ᵥ (fun i => (r i : ℝ)) := by
    rw [← dotProduct_transpose_mulVec, gramReal_symm, hs]
  change _ = _ at hb
  unfold quadratic
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hs, hp, hc, hn]
  change (quadratic (gramReal D) (fun i => (n i : ℝ))) + _ + _ = _
  rw [hb]
  have he : (bilinear D n n : ℝ) = 2 * (chargeEnergy D n : ℝ) := by
    exact_mod_cast (two_chargeEnergy D n).symm
  rw [he]
  push_cast
  ring

private lemma term_T (D : LatticeData) (hD : (gramReal D).PosDef)
    (r n : Charge D) (τ : ℂ) :
    Complex.exp (Real.pi * Complex.I * (τ+1) *
      (quadratic (gramReal D) ((fun i => (n i : ℝ)) + shift D r) : ℂ)) =
    phase ((pairRaw D r r / 2 : ℚ) : QmodZ) *
      Complex.exp (Real.pi * Complex.I * τ *
        (quadratic (gramReal D) ((fun i => (n i : ℝ)) + shift D r) : ℂ)) := by
  rw [show Real.pi * Complex.I * (τ+1) *
      (quadratic (gramReal D) ((fun i => (n i : ℝ)) + shift D r) : ℂ) =
      Real.pi * Complex.I *
        (quadratic (gramReal D) ((fun i => (n i : ℝ)) + shift D r) : ℂ) +
      Real.pi * Complex.I * τ *
        (quadratic (gramReal D) ((fun i => (n i : ℝ)) + shift D r) : ℂ) by ring,
    Complex.exp_add]
  congr 1
  rw [phase_mk, quadratic_shift_expansion D hD]
  push_cast
  rw [show (Real.pi : ℂ) * Complex.I *
      ((pairRaw D r r : ℂ) + 2 * ((n ⬝ᵥ r : ℤ) + (chargeEnergy D n : ℤ))) =
      2 * Real.pi * Complex.I * ((pairRaw D r r : ℂ) / 2) +
        (((n ⬝ᵥ r + chargeEnergy D n : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) by
      push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma summable_coset_norm (D : LatticeData) (hD : (gramReal D).PosDef)
    (r : Charge D) (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun n : Charge D => ‖Complex.exp (Real.pi * Complex.I * τ *
      (quadratic (gramReal D) ((fun i => (n i : ℝ)) + shift D r) : ℂ))‖) := by
  have hi : Function.Injective (fun n : Charge D => r + gramMap D n) := by
    intro m n h
    exact gramMap_injective D hD (add_left_cancel h)
  have hs := (summable_norm_theta (gramReal D)⁻¹ hD.inv τ hτ).comp_injective hi
  simpa only [Function.comp_def, inverse_quadratic_coset D hD] using hs

/-- Exact dissection of the inverse Gram theta into all original discriminant sectors. -/
theorem inverse_theta_dissection (D : LatticeData) (hD : (gramReal D).PosDef)
    (τ : ℂ) (hτ : 0 < τ.im) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    theta (gramReal D)⁻¹ τ = ∑ a : Discriminant D, sectorTheta D a τ := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  let f := fun k : Charge D => Complex.exp (Real.pi * Complex.I * τ *
    (quadratic (gramReal D)⁻¹ (fun i => (k i : ℝ)) : ℂ))
  have hs : Summable f := (summable_norm_theta (gramReal D)⁻¹ hD.inv τ hτ).of_norm
  have hp : Summable (fun p : Discriminant D × Charge D => f (cosetEquiv D hD p)) :=
    hs.comp_injective (cosetEquiv D hD).injective
  calc
    theta (gramReal D)⁻¹ τ = ∑' p, f (cosetEquiv D hD p) :=
      ((cosetEquiv D hD).tsum_eq f).symm
    _ = ∑' a : Discriminant D, ∑' n : Charge D, f (cosetEquiv D hD (a,n)) := hp.tsum_prod
    _ = ∑ a : Discriminant D, sectorTheta D a τ := by
      simp only [f, cosetEquiv_apply, inverse_quadratic_coset D hD,
        sectorTheta, representativeTheta, tsum_fintype]

private lemma shift_add_gram (D : LatticeData) (hD : (gramReal D).PosDef)
    (r m : Charge D) :
    shift D (r + gramMap D m) = shift D r + (fun i => (m i : ℝ)) := by
  simp only [shift_eq D hD]
  have hc : (fun i => ((r + gramMap D m) i : ℝ)) =
      (fun i => (r i : ℝ)) + gramReal D *ᵥ (fun i => (m i : ℝ)) := by
    rw [← cast_gram]
    ext i
    simp
  rw [hc, mulVec_add, mulVec_mulVec, nonsing_inv_mul _ (real_unit D hD), one_mulVec]

private lemma theta_add_gram (D : LatticeData) (hD : (gramReal D).PosDef)
    (r m : Charge D) (τ : ℂ) (hτ : 0 < τ.im) :
    representativeTheta D (r + gramMap D m) τ = representativeTheta D r τ := by
  let f := fun n : Charge D => Complex.exp (Real.pi * Complex.I * τ *
    (quadratic (gramReal D) ((fun i => (n i : ℝ)) + shift D r) : ℂ))
  have hs : Summable f := (summable_coset_norm D hD r τ hτ).of_norm
  have he : (fun n : Charge D => Complex.exp (Real.pi * Complex.I * τ *
      (quadratic (gramReal D) ((fun i => (n i : ℝ)) + shift D (r + gramMap D m)) : ℂ))) =
      f ∘ (Equiv.addRight m) := by
    funext n
    dsimp [f]
    rw [shift_add_gram D hD]
    have hv : (fun i => (n i : ℝ)) + (shift D r + fun i => (m i : ℝ)) =
        (fun i => ((n+m) i : ℝ)) + shift D r := by
      ext i
      simp [add_assoc, add_comm, add_left_comm]
    rw [hv]
    rfl
  change (∑' n, _) = ∑' n, f n
  rw [he]
  exact ((Equiv.addRight m).hasSum_iff.mpr hs.hasSum).tsum_eq

/-- Every representative gives the same absolutely convergent literal sector series. -/
theorem sector_summable_representative (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Discriminant D) (r : Charge D) (hr : classOf D r = a)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun n : Charge D => ‖Complex.exp (Real.pi * Complex.I * τ *
      (quadratic (gramReal D) ((fun i => (n i : ℝ)) + shift D r) : ℂ))‖) ∧
      sectorTheta D a τ = representativeTheta D r τ := by
  refine ⟨summable_coset_norm D hD r τ hτ, ?_⟩
  have hm : representative D a - r ∈ gramRange D :=
    (Submodule.Quotient.eq _).mp ((class_representative D a).trans hr.symm)
  obtain ⟨m, hm⟩ := hm
  have he : representative D a = r + gramMap D m := by
    change gramMap D m = representative D a - r at hm
    rw [hm]
    abel
  rw [sectorTheta, he]
  exact theta_add_gram D hD r m τ hτ

private lemma zero_sector (D : LatticeData) (hD : (gramReal D).PosDef)
    (τ : ℂ) (hτ : 0 < τ.im) : sectorTheta D 0 τ = theta (gramReal D) τ := by
  rw [(sector_summable_representative D hD 0 0 rfl τ hτ).2]
  have hz : shift D 0 = 0 := by
    rw [shift_eq D hD]
    ext i
    simp [mulVec, dotProduct]
  simp only [representativeTheta, hz, add_zero, theta]

/-- The original zero-sector S row has all discriminant sectors on its right. -/
theorem zero_sector_S (D : LatticeData) (hD : (gramReal D).PosDef)
    (τ : ℂ) (hτ : 0 < τ.im) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    sectorTheta D 0 (-1 / τ) = (-Complex.I * τ) ^ ((D.rank : ℂ) / 2) /
      (Real.sqrt (gramReal D).det : ℂ) * ∑ a : Discriminant D, sectorTheta D a τ := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  have hτ0 : τ ≠ 0 := by intro h; simpa [h] using hτ
  have hi : 0 < (-1 / τ).im := by
    rw [neg_div, one_div, Complex.neg_im, Complex.inv_im]
    simpa only [neg_div, neg_neg] using div_pos hτ (Complex.normSq_pos.mpr hτ0)
  rw [zero_sector D hD _ hi, theta_inversion (gramReal D) hD τ hτ,
    inverse_theta_dissection D hD τ hτ]

/-- Original integral evenness supplies the full discriminant-class T multiplier. -/
theorem sector_T (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Discriminant D) (τ : ℂ) (hτ : 0 < τ.im) :
    sectorTheta D a (τ+1) = phase (quadraticClass D a) * sectorTheta D a τ := by
  have hs := (summable_coset_norm D hD (representative D a) τ hτ).of_norm.hasSum
  have ht := hs.mul_left (phase (quadraticClass D a))
  simpa only [quadraticClass, ← term_T D hD (representative D a), representativeTheta,
    sectorTheta] using ht.tsum_eq

private lemma pairing_neg (D : LatticeData) (hD : (gramReal D).PosDef)
    (a c : Discriminant D) : pairing D (-a) c = -pairing D a c := by
  have h := pairing_add D hD (-a) a c
  rw [neg_add_cancel, pairing_zero D hD] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The character supplied by the original inverse-Gram discriminant pairing. -/
def pairingCharacter (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Discriminant D) : AddChar (Discriminant D) ℂ where
  toFun c := phase (pairing D a c)
  map_zero_eq_one' := by rw [pairing_symm, pairing_zero D hD]; exact phase.map_zero_eq_one
  map_add_eq_mul' c d := by
    rw [pairing_symm D a, pairing_add D hD, pairing_symm D c, pairing_symm D d]
    exact phase.map_add_eq_mul _ _

private lemma character_symm (D : LatticeData) (hD : (gramReal D).PosDef)
    (a c : Discriminant D) : pairingCharacter D hD a c = pairingCharacter D hD c a := by
  exact congrArg phase (pairing_symm D a c)

private lemma character_zero_iff (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Discriminant D) : pairingCharacter D hD a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply pairing_nondegenerate D hD a
    intro c
    apply phase_injective
    change pairingCharacter D hD a c = phase 0
    rw [h]
    simp
  · rintro rfl
    ext c
    simp [pairingCharacter, pairing_zero D hD]

private lemma character_injective (D : LatticeData) (hD : (gramReal D).PosDef) :
    Function.Injective (pairingCharacter D hD) := by
  intro a b h
  apply sub_eq_zero.mp
  apply pairing_nondegenerate D hD (a-b)
  intro c
  have hc : pairing D a c = pairing D b c := phase_injective (congrArg (fun f => f c) h)
  rw [sub_eq_add_neg, pairing_add D hD, pairing_neg D hD, hc, add_neg_cancel]

/-- All complex characters are obtained from this particular lattice pairing. -/
def characterEquiv (D : LatticeData) (hD : (gramReal D).PosDef) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    Discriminant D ≃ AddChar (Discriminant D) ℂ := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  exact Equiv.ofBijective (pairingCharacter D hD)
    ((Fintype.bijective_iff_injective_and_card (pairingCharacter D hD)).mpr
      ⟨character_injective D hD, (AddChar.card_eq (α := Discriminant D)).symm⟩)

private lemma character_orthogonality (D : LatticeData) (hD : (gramReal D).PosDef)
    (c : Discriminant D) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    letI : DecidableEq (Discriminant D) := Classical.decEq _
    ∑ a : Discriminant D, pairingCharacter D hD a c =
      if c = 0 then (D.G.det.natAbs : ℂ) else 0 := by
  classical
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  simp_rw [character_symm D hD]
  rw [AddChar.sum_eq_ite]
  simp only [character_zero_iff D hD]
  rw [← Nat.card_eq_fintype_card, discriminant_card D hD]

/-- Literal inverse-theta coefficients resolved by the negative pairing character. -/
def inverseCoefficient (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Discriminant D) (τ : ℂ) : ℂ :=
  ∑' k : Charge D, pairingCharacter D hD a (-classOf D k) *
    Complex.exp (Real.pi * Complex.I * τ *
      (quadratic (gramReal D)⁻¹ (fun i => (k i : ℝ)) : ℂ))

private lemma coefficient_norm_summable (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Discriminant D) (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun k : Charge D => ‖pairingCharacter D hD a (-classOf D k) *
      Complex.exp (Real.pi * Complex.I * τ *
        (quadratic (gramReal D)⁻¹ (fun i => (k i : ℝ)) : ℂ))‖) := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  simpa only [norm_mul, AddChar.norm_apply, one_mul] using
    summable_norm_theta (gramReal D)⁻¹ hD.inv τ hτ

private lemma coefficient_resolution (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Discriminant D) (τ : ℂ) (hτ : 0 < τ.im) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    inverseCoefficient D hD a τ = ∑ c : Discriminant D,
      pairingCharacter D hD a (-c) * sectorTheta D c τ := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  let f := fun k : Charge D => pairingCharacter D hD a (-classOf D k) *
    Complex.exp (Real.pi * Complex.I * τ *
      (quadratic (gramReal D)⁻¹ (fun i => (k i : ℝ)) : ℂ))
  have hs : Summable f := (coefficient_norm_summable D hD a τ hτ).of_norm
  have hp := hs.comp_injective (cosetEquiv D hD).injective
  calc
    inverseCoefficient D hD a τ = ∑' p, f (cosetEquiv D hD p) :=
      ((cosetEquiv D hD).tsum_eq f).symm
    _ = ∑' c : Discriminant D, ∑' n : Charge D, f (cosetEquiv D hD (c,n)) := hp.tsum_prod
    _ = ∑ c : Discriminant D, pairingCharacter D hD a (-c) * sectorTheta D c τ := by
      simp only [f, cosetEquiv_apply, inverse_quadratic_coset D hD,
        class_add, class_gram, class_representative, add_zero, tsum_mul_left,
        tsum_fintype, sectorTheta, representativeTheta]

/-- Absolute convergence, finite character resolution and reconstruction of actual inverse coefficients. -/
theorem inverse_theta_fourier (D : LatticeData) (hD : (gramReal D).PosDef)
    (τ : ℂ) (hτ : 0 < τ.im) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    (∀ a : Discriminant D,
      Summable (fun k : Charge D => ‖pairingCharacter D hD a (-classOf D k) *
        Complex.exp (Real.pi * Complex.I * τ *
          (quadratic (gramReal D)⁻¹ (fun i => (k i : ℝ)) : ℂ))‖) ∧
      inverseCoefficient D hD a τ = ∑ c : Discriminant D,
        pairingCharacter D hD a (-c) * sectorTheta D c τ) ∧
    (∀ c : Discriminant D, (D.G.det.natAbs : ℂ) * sectorTheta D c τ =
      ∑ a : Discriminant D, pairingCharacter D hD a c * inverseCoefficient D hD a τ) := by
  classical
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  refine ⟨fun a => ⟨coefficient_norm_summable D hD a τ hτ,
    coefficient_resolution D hD a τ hτ⟩, ?_⟩
  intro c
  simp_rw [coefficient_resolution D hD _ τ hτ, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← AddChar.map_add_eq_mul, ← Finset.sum_mul,
    character_orthogonality D hD]
  simp only [add_neg_eq_zero]
  simp

end
end D5.S3.VertexAlgebra.LatticeDiscriminantTheta
