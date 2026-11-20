import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundary
import Reg.Support.SingleDependentReadout

/-! Source observation of the reciprocal-zeta mass on a fixed vertical line. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex MeasureTheory Set
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.MobiusDyadicEnergy (mobiusDyadicDifference)
open _root_.D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundary
open _root_.D5.S3.Weil.ZetaPntBounds.MobiusDyadicUnitWeightParseval
  (measurable_unitWeight_difference mobiusDyadicDifference_unitWeight_parseval)

namespace Reg.D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundary

private def energyDensity (θ x : ℝ) : ℝ :=
  mobiusDyadicDifference x ^ 2 * x ^ (-(2 * θ - 1))

private def reciprocalDensity (θ y : ℝ) : ℝ :=
  1 / ((1 + |y|) ^ 2 * ‖riemannZeta ((θ : ℂ) + (y : ℂ) * I)‖ ^ 2)

private def bound (θ : ℝ) : ℝ :=
  4 + 4 * Real.pi * (∫ x in Ioi (1 : ℝ), energyDensity θ x) / (1 - (2 : ℝ) ^ (θ - 1)) ^ 2

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ f => integral volume f) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => bound (3 / 2) + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {θ : ℝ}, 0 ≤ θ → θ < 2 → θ ≠ 1 →
    (∀ y : ℝ, riemannZeta ((θ : ℂ) + (y : ℂ) * I) ≠ 0) →
    IntegrableOn (energyDensity θ) (Ioi 1) →
    Integrable (reciprocalDensity θ) ∧ R.readout () () (reciprocalDensity θ) ≤ bound θ

private theorem energy_three_halves : IntegrableOn (energyDensity (3 / 2)) (Ioi 1) := by
  refine mobiusDyadicDifference_unitWeight_parseval.1.mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    exact (measurable_unitWeight_difference.pow_const (2 : ℕ)).mul
      (by fun_prop : Measurable (fun x : ℝ => x ^ (-(2 * (3 / 2 : ℝ) - 1))))
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (1 : ℝ)))] with x hx
    have hx₁ : 1 ≤ x := hx.le
    have hx₀ : 0 ≤ x := zero_le_one.trans hx₁
    have hpow : x ^ (-(2 * (3 / 2 : ℝ) - 1)) ≤ x⁻¹ := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hx₁ (by norm_num)
    rw [energyDensity, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg hx₀ _))]
    exact mul_le_mul_of_nonneg_left hpow (sq_nonneg _)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero (y : ℝ) : riemannZeta (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    norm_num [Complex.add_re, Complex.mul_re]
  have hfalse := (h (by norm_num) (by norm_num) (by norm_num) hzero energy_three_halves).2
  change bound (3 / 2) + 1 ≤ bound (3 / 2) at hfalse
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (Icc (0 : ℝ) 1).indicator 1, ?_⟩
  change (∫ _ : ℝ, (0 : ℝ)) ≠ ∫ y : ℝ, (Icc (0 : ℝ) 1).indicator 1 y
  rw [integral_zero, integral_indicator_one measurableSet_Icc, Real.volume_real_Icc]
  norm_num

def family : Registration arena
    (type_of% @weighted_reciprocal_zeta_sq_bound_of_mobiusDyadicEnergy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_reciprocal_zeta_sq_bound_of_mobiusDyadicEnergy, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weighted_reciprocal_zeta_sq_bound_of_mobiusDyadicEnergy)
    (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundary.weighted_reciprocal_zeta_sq_bound_of_mobiusDyadicEnergy.audit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => integral volume f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundary
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundary
