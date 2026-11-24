/- GID: D5/S3/VertexAlgebra/TwistedGround/ActualLeechGroundConjugation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/ActualLeechGroundConjugation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equivariant conjugation on the actual Leech twisted ground from its selected pairing. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic
import D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry
import D5.S3.VertexAlgebra.TwistedGround.Charge.ChargeHermitian
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! The selected BPZ ground form identifies the positive charge Hermitian
functional with an equivariant antilinear operator on the actual ground. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.ActualLeechGroundConjugation

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeHalfFockChargedTensorCoefficients
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open ChargeHermitian

open private selectedGroundPairing from
  D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open private ground_pairing_symmetric from
  D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry

private abbrev leechUnit : IsUnit leechData.G.det := leech_spec.2.1

private abbrev groundForm := (selectedGroundPairing leechData leechUnit).form

local notation "V" => ActualGround leechData leechUnit
local notation "ρ" => groundRepresentation leechData leechUnit
local notation "G" => (Extension leechData ⧸ K leechData)
local notation "pairing" => selectedGroundPairing leechData leechUnit
local notation "B" => groundForm
local notation "H" => chargeForm leechData ρ

private def chargeDual : V →ₗ⋆[ℂ] Module.Dual ℂ V where
  toFun x :=
    { toFun := H x
      map_add' := charge_form_add_right leechData ρ x
      map_smul' := fun c y => charge_form_smul_right leechData ρ c x y }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    exact charge_form_add_left leechData ρ x z y
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    exact charge_form_smul_left leechData ρ c x y

/-- Identify the charge Hermitian functional with a vector using the selected bilinear form. -/
def leechGroundRiesz : V →ₗ⋆[ℂ] V :=
  ((B).toDual (pairing).nondegenerate).symm.toLinearMap.comp chargeDual

local notation "J" => leechGroundRiesz

theorem leechGroundRiesz_pairing (x y : V) : B (J x) y = H x y := by
  change B (((B).toDual (pairing).nondegenerate).symm (chargeDual x)) y =
    chargeDual x y
  exact LinearMap.BilinForm.apply_toDual_symm_apply (chargeDual x) y

theorem leechGroundRiesz_equivariant (g : G) (x : V) :
    J (ρ g x) = ρ g (J x) := by
  have central : ρ (QuotientGroup.mk (⟨1, 0⟩ : Extension leechData)) =
      -(1 : Module.End ℂ V) :=
    (Classical.choose_spec
      (Classical.choose_spec (actual_twisted_ground_representation leechData leechUnit))).2.2.1
  apply ((B).toDual (pairing).nondegenerate).injective
  apply LinearMap.ext
  intro y
  change B (J (ρ g x)) y = B (ρ g (J x)) y
  calc
    B (J (ρ g x)) y = H (ρ g x) y := leechGroundRiesz_pairing _ _
    _ = H x (ρ g⁻¹ y) := charge_form_inverse_adjoint leechData ρ central g x y
    _ = B (J x) (ρ g⁻¹ y) := (leechGroundRiesz_pairing _ _).symm
    _ = B (ρ g (J x)) y := by
      simpa only [(ρ).self_inv_apply] using
        ((pairing).invariant g (J x) (ρ g⁻¹ y)).symm

theorem leechGroundRiesz_positive (x : V) (hx : x ≠ 0) :
    (B (J x) x).im = 0 ∧ 0 < (B (J x) x).re := by
  rw [leechGroundRiesz_pairing]
  exact ⟨charge_form_im_self leechData ρ x, charge_form_positive leechData ρ x hx⟩

/-- The square has a stable complex eigenspace, and the selected symmetry gives the
Hermitian diagonal identity that determines its scalar. -/
theorem leechGroundRiesz_square :
    ∃ a : ℝ, 0 < a ∧
      (∀ x : V, J (J x) = (a : ℂ) • x) ∧
      (∀ x : V, H (J x) (J x) = (a : ℂ) * H x x) := by
  haveI : (ρ).IsIrreducible :=
    (Classical.choose_spec
      (Classical.choose_spec (actual_twisted_ground_representation leechData leechUnit))).2.1
  haveI : Nonempty (Half (groundRank leechData leechUnit)) := ⟨0⟩
  let square : Module.End ℂ V := leechGroundRiesz.comp leechGroundRiesz
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue square
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  obtain ⟨hv_mem, hv_ne⟩ := Module.End.hasEigenvector_iff.mp hv
  let eigenspace : Subrepresentation ρ :=
    { toSubmodule := square.eigenspace a
      apply_mem_toSubmodule g := by
        intro x hx
        have he := Module.End.mem_eigenspace_iff.mp hx
        apply Module.End.mem_eigenspace_iff.mpr
        change J (J (ρ g x)) = a • ρ g x
        change J (J x) = a • x at he
        rw [leechGroundRiesz_equivariant g x, leechGroundRiesz_equivariant g (J x),
          he, map_smul] }
  have eigenspace_top : eigenspace = ⊤ := by
    refine (eq_bot_or_eq_top eigenspace).resolve_left ?_
    intro bottom
    have member : v ∈ eigenspace := hv_mem
    rw [bottom] at member
    change v ∈ (⊥ : Submodule ℂ V) at member
    exact hv_ne ((Submodule.mem_bot ℂ).mp member)
  have square_apply (x : V) : J (J x) = a • x := by
    have member : x ∈ eigenspace := by
      rw [eigenspace_top]
      change x ∈ (⊤ : Submodule ℂ V)
      exact Submodule.mem_top
    exact Module.End.mem_eigenspace_iff.mp (show x ∈ square.eigenspace a from member)
  have symmetric := ground_pairing_symmetric leechData leechUnit pairing
  have diagonal (x : V) : H (J x) (J x) = a * H x x := by
    calc
      H (J x) (J x) = B (J (J x)) (J x) := (leechGroundRiesz_pairing _ _).symm
      _ = B (J x) (J (J x)) := symmetric.eq _ _
      _ = a * H x x := by
        rw [square_apply x, LinearMap.BilinForm.smul_right, leechGroundRiesz_pairing]
  have positive : 0 < (H v v).re := by
    rw [← leechGroundRiesz_pairing]
    exact (leechGroundRiesz_positive v hv_ne).2
  have hJv : J v ≠ 0 := by
    intro zero
    have h : H v v = 0 := by
      rw [← leechGroundRiesz_pairing v v, zero, LinearMap.BilinForm.zero_left]
    exact positive.ne' (congrArg Complex.re h)
  have imaginary : a.im = 0 := by
    have h : 0 = a.im * (H v v).re := by
      simpa only [Complex.mul_im, charge_form_im_self leechData ρ, mul_zero, zero_add]
        using congrArg Complex.im (diagonal v)
    exact (mul_eq_zero.mp h.symm).resolve_right positive.ne'
  have real_part : (H (J v) (J v)).re = a.re * (H v v).re := by
    simpa only [Complex.mul_re, charge_form_im_self leechData ρ, mul_zero, sub_zero]
      using congrArg Complex.re (diagonal v)
  have scalar_positive : 0 < a.re := by
    apply (mul_pos_iff_of_pos_right positive).mp
    rw [← real_part]
    exact charge_form_positive leechData ρ (J v) hJv
  have scalar_real : (a.re : ℂ) = a := Complex.ext rfl imaginary.symm
  exact ⟨a.re, scalar_positive,
    fun x => by rw [scalar_real, square_apply],
    fun x => by rw [scalar_real, diagonal]⟩

/-- The inverse positive square root of the Riesz square gives an equivariant
conjugation whose selected-pairing evaluation is positive on nonzero ground states. -/
theorem leechGroundConjugation :
    ∃ (a : ℝ) (C : V →ₗ⋆[ℂ] V), 0 < a ∧
      (∀ x : V, C x = (((Real.sqrt a)⁻¹ : ℝ) : ℂ) • J x) ∧
      (∀ x : V, C (C x) = x) ∧
      (∀ (g : G) (x : V), C (ρ g x) = ρ g (C x)) ∧
      (∀ x y : V, B (C x) y = (((Real.sqrt a)⁻¹ : ℝ) : ℂ) * H x y) ∧
      (∀ x : V, x ≠ 0 → (B (C x) x).im = 0 ∧ 0 < (B (C x) x).re) := by
  obtain ⟨a, ha, square_apply, _⟩ := leechGroundRiesz_square
  let r : ℝ := Real.sqrt a
  have hr : 0 < r := Real.sqrt_pos.mpr ha
  have hr_sq : r * r = a := Real.mul_self_sqrt ha.le
  have scale_real : r⁻¹ * (r⁻¹ * a) = 1 := by
    calc
      r⁻¹ * (r⁻¹ * a) = r⁻¹ * ((r⁻¹ * r) * r) := by
        rw [← hr_sq, mul_assoc r⁻¹ r r]
      _ = 1 := by simp only [inv_mul_cancel₀ hr.ne', one_mul]
  have scale : ((r⁻¹ : ℝ) : ℂ) * (((r⁻¹ : ℝ) : ℂ) * (a : ℂ)) = 1 := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_one] using
      congrArg Complex.ofReal scale_real
  let C : V →ₗ⋆[ℂ] V := ((r⁻¹ : ℝ) : ℂ) • J
  have scaled_apply (x : V) : C x = ((r⁻¹ : ℝ) : ℂ) • J x := rfl
  have evaluation (x y : V) : B (C x) y = ((r⁻¹ : ℝ) : ℂ) * H x y := by
    rw [scaled_apply, LinearMap.BilinForm.smul_left, leechGroundRiesz_pairing]
  refine ⟨a, C, ha, scaled_apply, ?_, ?_, evaluation, ?_⟩
  · intro x
    simp only [scaled_apply, map_smulₛₗ, Complex.conj_ofReal, square_apply, smul_smul,
      scale, one_smul]
  · intro g x
    simp only [scaled_apply, leechGroundRiesz_equivariant, map_smul]
  · intro x hx
    rw [evaluation]
    constructor
    · simp only [Complex.im_ofReal_mul, charge_form_im_self leechData ρ x, mul_zero]
    · simpa only [Complex.re_ofReal_mul]
        using mul_pos (inv_pos.mpr hr) (charge_form_positive leechData ρ x hx)

end D5.S3.VertexAlgebra.TwistedGround.ActualLeechGroundConjugation
