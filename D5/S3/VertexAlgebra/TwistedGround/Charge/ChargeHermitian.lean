/- GID: D5/S3/VertexAlgebra/TwistedGround/Charge/ChargeHermitian
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Charge/ChargeHermitian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Canonical charge averaging gives positive invariant ground Hermitian geometry. -/

import D5.S3.VertexAlgebra.TwistedGround.Charge.ChargeGeometry
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.ChargeHermitian

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient TwistedGround.OperatorAlgebra
open TwistedGround.ChargeGeometry
open scoped BigOperators

noncomputable section

def coordinateForm {rank : ℕ} (first second : Ground rank) : ℂ :=
  ∑ coordinate : Half rank, starRingEnd ℂ (first coordinate) * second coordinate

def chargeForm (D : LatticeData) {rank : ℕ}
    (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank))
    (first second : Ground rank) : ℂ :=
  (Fintype.card (ModTwoCharge D) : ℂ)⁻¹ *
    ∑ charge : ModTwoCharge D,
      coordinateForm (chargeOperator D rho charge first) (chargeOperator D rho charge second)

variable (D : LatticeData) {rank : ℕ}
variable (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank))

private theorem coordinate_sign (scalar : ℂ) (unit : starRingEnd ℂ scalar * scalar = 1)
    (first second : Ground rank) :
    coordinateForm (scalar • first) (scalar • second) = coordinateForm first second := by
  apply Finset.sum_congr rfl
  intro coordinate membership
  change starRingEnd ℂ (scalar * first coordinate) * (scalar * second coordinate) = _
  rw [map_mul]
  calc
    starRingEnd ℂ scalar * starRingEnd ℂ (first coordinate) * (scalar * second coordinate) =
        (starRingEnd ℂ scalar * scalar) *
          (starRingEnd ℂ (first coordinate) * second coordinate) := by ring
    _ = _ := by rw [unit, one_mul]

theorem charge_form_add_left (first second third : Ground rank) :
    chargeForm D rho (first + second) third =
      chargeForm D rho first third + chargeForm D rho second third := by
  simp [chargeForm, coordinateForm, map_add, add_mul, Finset.sum_add_distrib, mul_add]

theorem charge_form_add_right (first second third : Ground rank) :
    chargeForm D rho first (second + third) =
      chargeForm D rho first second + chargeForm D rho first third := by
  simp [chargeForm, coordinateForm, map_add, mul_add, Finset.sum_add_distrib]

theorem charge_form_smul_left (scalar : ℂ) (first second : Ground rank) :
    chargeForm D rho (scalar • first) second =
      starRingEnd ℂ scalar * chargeForm D rho first second := by
  simp only [chargeForm, coordinateForm, map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

theorem charge_form_smul_right (scalar : ℂ) (first second : Ground rank) :
    chargeForm D rho first (scalar • second) = scalar * chargeForm D rho first second := by
  simp only [chargeForm, coordinateForm, map_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (starRingEnd ℂ _) scalar, ← Finset.mul_sum]
  ring

theorem charge_form_hermitian (first second : Ground rank) :
    starRingEnd ℂ (chargeForm D rho first second) = chargeForm D rho second first := by
  simp only [chargeForm, coordinateForm, map_mul, map_sum, map_inv₀, map_natCast,
    starRingEnd_self_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro charge membership
  apply Finset.sum_congr rfl
  intro coordinate membership
  exact mul_comm _ _

theorem charge_form_diagonal (state : Ground rank) :
    chargeForm D rho state state =
      (((Fintype.card (ModTwoCharge D) : ℝ)⁻¹ *
        ∑ charge : ModTwoCharge D, ∑ coordinate : Half rank,
          Complex.normSq (chargeOperator D rho charge state coordinate) : ℝ) : ℂ) := by
  simp only [chargeForm, coordinateForm, ← Complex.normSq_eq_conj_mul_self]
  push_cast
  rfl

theorem charge_form_im_self (state : Ground rank) : (chargeForm D rho state state).im = 0 := by
  rw [charge_form_diagonal]
  rfl

theorem charge_form_nonnegative (state : Ground rank) :
    0 ≤ (chargeForm D rho state state).re := by
  rw [charge_form_diagonal]
  change 0 ≤ (Fintype.card (ModTwoCharge D) : ℝ)⁻¹ * _
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_nonneg fun charge _ =>
    Finset.sum_nonneg fun coordinate _ => Complex.normSq_nonneg _

theorem charge_form_positive (state : Ground rank) (nonzero : state ≠ 0) :
    0 < (chargeForm D rho state state).re := by
  classical
  have coordinate_exists : ∃ coordinate, state coordinate ≠ 0 := by
    by_contra absent
    push Not at absent
    exact nonzero (funext absent)
  obtain ⟨coordinate, value⟩ := coordinate_exists
  rw [charge_form_diagonal]
  change 0 < (Fintype.card (ModTwoCharge D) : ℝ)⁻¹ * _
  apply mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  apply (Finset.sum_pos_iff_of_nonneg (fun charge _ =>
    Finset.sum_nonneg fun index _ => Complex.normSq_nonneg _)).mpr
  refine ⟨0, Finset.mem_univ _, ?_⟩
  simp only [charge_zero, Module.End.one_apply]
  exact (Finset.sum_pos_iff_of_nonneg (fun index _ => Complex.normSq_nonneg _)).mpr
    ⟨coordinate, Finset.mem_univ _, Complex.normSq_pos.mpr value⟩

theorem charge_form_left_radical (state : Ground rank) :
    (∀ other, chargeForm D rho state other = 0) ↔ state = 0 := by
  constructor
  · intro radical
    by_contra nonzero
    have positive := charge_form_positive D rho state nonzero
    rw [radical] at positive
    norm_num at positive
  · rintro rfl other
    simp [chargeForm, coordinateForm]

theorem charge_form_right_radical (state : Ground rank) :
    (∀ other, chargeForm D rho other state = 0) ↔ state = 0 := by
  constructor
  · intro radical
    by_contra nonzero
    have positive := charge_form_positive D rho state nonzero
    rw [radical] at positive
    norm_num at positive
  · rintro rfl other
    simp [chargeForm, coordinateForm]

variable (central : rho (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
  -(1 : Module.End ℂ (Ground rank)))

include central in
theorem charge_form_invariant (element : Extension D ⧸ K D) (first second : Ground rank) :
    chargeForm D rho (rho element first) (rho element second) = chargeForm D rho first second := by
  classical
  unfold chargeForm
  congr 1
  calc
    _ = ∑ charge : ModTwoCharge D,
        coordinateForm (chargeOperator D rho (charge + quotientCharge D element) first)
          (chargeOperator D rho (charge + quotientCharge D element) second) := by
      apply Finset.sum_congr rfl
      intro charge membership
      have first_translation := congrArg (fun operator : Module.End ℂ (Ground rank) =>
        operator first) (charge_right_translation D rho central charge element)
      have second_translation := congrArg (fun operator : Module.End ℂ (Ground rank) =>
        operator second) (charge_right_translation D rho central charge element)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at first_translation second_translation
      rw [first_translation, second_translation]
      exact coordinate_sign _ (translation_sign_unit D charge element) _ _
    _ = _ := Fintype.sum_equiv (Equiv.addRight (quotientCharge D element)) _ _ (fun _ => rfl)

include central in
theorem charge_form_inverse_adjoint (element : Extension D ⧸ K D)
    (first second : Ground rank) :
    chargeForm D rho (rho element first) second =
      chargeForm D rho first (rho element⁻¹ second) := by
  have invariant := charge_form_invariant D rho central element first (rho element⁻¹ second)
  simpa only [rho.self_inv_apply] using invariant

#print axioms charge_form_positive
#print axioms charge_form_invariant
#print axioms charge_form_inverse_adjoint

structure GroundHermitian (form : Ground rank → Ground rank → ℂ) : Prop where
  canonical : form = chargeForm D rho
  add_left : ∀ first second third, form (first + second) third =
    form first third + form second third
  add_right : ∀ first second third, form first (second + third) =
    form first second + form first third
  smul_left : ∀ scalar first second, form (scalar • first) second =
    starRingEnd ℂ scalar * form first second
  smul_right : ∀ scalar first second, form first (scalar • second) =
    scalar * form first second
  hermitian : ∀ first second, starRingEnd ℂ (form first second) = form second first
  diagonal_real : ∀ state, (form state state).im = 0
  nonnegative : ∀ state, 0 ≤ (form state state).re
  positive : ∀ state, state ≠ 0 → 0 < (form state state).re
  left_radical : ∀ state, (∀ other, form state other = 0) ↔ state = 0
  right_radical : ∀ state, (∀ other, form other state = 0) ↔ state = 0
  invariant : ∀ element first second,
    form (rho element first) (rho element second) = form first second
  inverse_adjoint : ∀ element first second,
    form (rho element first) second = form first (rho element⁻¹ second)

include central in
theorem actual_charge_geometry : GroundHermitian D rho (chargeForm D rho) where
  canonical := rfl
  add_left := charge_form_add_left D rho
  add_right := charge_form_add_right D rho
  smul_left := charge_form_smul_left D rho
  smul_right := charge_form_smul_right D rho
  hermitian := charge_form_hermitian D rho
  diagonal_real := charge_form_im_self D rho
  nonnegative := charge_form_nonnegative D rho
  positive := charge_form_positive D rho
  left_radical := charge_form_left_radical D rho
  right_radical := charge_form_right_radical D rho
  invariant := charge_form_invariant D rho central
  inverse_adjoint := charge_form_inverse_adjoint D rho central

#print axioms actual_charge_geometry

end

end D5.S3.VertexAlgebra.TwistedGround.ChargeHermitian
