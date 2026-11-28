import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.PlanarSublevelSandwich
import Mathlib.Tactic.NormNum
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the integral of the minorant. -/

namespace Reg.D5.S3.Fourier.Asymptotics.PlanarSublevelSandwich

open _root_.D5.S3.Fourier.Asymptotics.PlanarSublevelSandwich
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory
open scoped ContDiff

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Plane → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ lower => ∫ u, lower u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ {f : Plane → Plane} {z : Plane} (A : Plane ≃L[ℝ] Plane),
      HasFDerivAt f (A : Plane →L[ℝ] Plane) z → f z = 0 →
      ∀ {η ρ σ : ℝ}, 0 < η → η < 1 → 0 < ρ → ρ < (1 + η)⁻¹ → (1 - η)⁻¹ < σ →
      let determinant := |LinearMap.det (A.toLinearEquiv : Plane →ₗ[ℝ] Plane)|
      ∃ (r : ℝ) (lower upper : Plane → ℝ), 0 < r ∧
        ContDiff ℝ ∞ lower ∧ ContDiff ℝ ∞ upper ∧
        HasCompactSupport lower ∧ HasCompactSupport upper ∧
        Real.pi * ρ ^ 2 / determinant ≤ R.readout () () lower ∧
        (∫ u, upper u) ≤ Real.pi * σ ^ 2 / determinant ∧
        ∀ ε > 0, ε * (‖(A.symm : Plane →L[ℝ] Plane)‖ * (1 + η)⁻¹) < r →
          ∀ u : Plane,
            lower u ≤ (if ε * ‖u‖ < r ∧ ‖f (z + ε • u)‖ < ε then 1 else 0) ∧
            (if ε * ‖u‖ < r ∧ ‖f (z + ε • u)‖ < ε then 1 else 0) ≤ upper u

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let A := ContinuousLinearEquiv.refl ℝ Plane
  obtain ⟨r, lower, upper, _, _, _, _, _, hbound, _⟩ :=
    h (f := id) (z := 0) A (hasFDerivAt_id 0) rfl
      (η := 1 / 2) (ρ := 1 / 2) (σ := 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hpos : 0 < Real.pi * (1 / 2 : ℝ) ^ 2 /
      |LinearMap.det (A.toLinearEquiv : Plane →ₗ[ℝ] Plane)| :=
    div_pos (mul_pos Real.pi_pos (by norm_num)) (abs_pos.mpr A.toLinearEquiv.isUnit_det'.ne_zero)
  exact (not_le_of_gt hpos) hbound

theorem dependence : ObservationalDependence signature actual := by
  intro i
  let s := Metric.ball (0 : Plane) 1
  refine ⟨(), 0, s.indicator 1, ?_⟩
  change (∫ u : Plane, (0 : Plane → ℝ) u) ≠ ∫ u : Plane, s.indicator 1 u
  rw [integral_indicator_one Metric.isOpen_ball.measurableSet]
  have hvol : volume.real s = Real.pi := by
    simp [s, Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [hvol]
  simpa only [Pi.zero_apply, integral_zero] using (ne_of_gt Real.pi_pos).symm

def source_registration : Registration arena (type_of% @smooth_local_ellipse_sandwich) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨smooth_local_ellipse_sandwich, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@smooth_local_ellipse_sandwich) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Fourier.Asymptotics.PlanarSublevelSandwich.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.PlanarSublevelSandwich.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ lower => ∫ u, lower u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.PlanarSublevelSandwich
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 15
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Fourier.Asymptotics.PlanarSublevelSandwich
