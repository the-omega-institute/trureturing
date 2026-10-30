import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.XuYangMillsRemainder.Result
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.XuYangMillsRemainder.Result
open _root_.D5.S3.Analytic.XuYangMillsRemainder.Result
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set Real MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 2 ≤ n →
    CompletelyMonotoneOn (fun x => (-1:ℝ)^n * D n (R.readout () () x) (-1))

theorem mills_neg_one_pos : 0 < millsRatio (-1) := by
  have hi : IntegrableOn (fun t : ℝ => exp (-t^2/2)) (Ioi (-1)) := by
    convert (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).integrableOn
      (s := Ioi (-1)) using 1
    ext t
    congr 1
    ring
  have : NeZero (volume (Ioi (-1:ℝ))) := ⟨by simp⟩
  unfold millsRatio
  exact mul_pos (exp_pos _) (integral_exp_pos hi)

private theorem small_coefficients :
    u 1 (-1) (-3) = 0 ∧ u 2 (-1) (-3) = 0 ∧ u 3 (-1) (-3) = -2 := by
  have hg1 : Gamma ((1:ℝ)+1/2) = (1/2)*Gamma (1/2) := by
    rw [show (1:ℝ)+1/2 = (1/2)+1 by ring, Gamma_add_one (by norm_num)]
  have hg2 : Gamma ((2:ℝ)+1/2) = (3/2)*((1/2)*Gamma (1/2)) := by
    rw [show (2:ℝ)+1/2 = ((1:ℝ)+1/2)+1 by ring, Gamma_add_one (by norm_num), hg1]
    ring
  have hg3 : Gamma ((3:ℝ)+1/2) = (5/2)*((3/2)*((1/2)*Gamma (1/2))) := by
    rw [show (3:ℝ)+1/2 = ((2:ℝ)+1/2)+1 by ring, Gamma_add_one (by norm_num), hg2]
    ring
  norm_num at hg1 hg2 hg3
  have hz : Gamma ((2:ℝ)⁻¹) ≠ 0 := ne_of_gt (Gamma_pos_of_pos (by positivity))
  constructor
  · norm_num [u, Finset.sum_range_succ, hg1, hg2, hg3]
    field_simp
    ring
  · constructor
    · norm_num [u, Finset.sum_range_succ, hg1, hg2, hg3]
      field_simp
      ring
    · norm_num [u, Finset.sum_range_succ, hg1, hg2, hg3]
      field_simp
      ring

theorem D_three_neg_one : D 3 (-1) (-1) = 3*millsRatio (-1) := by
  have hu := small_coefficients
  norm_num [D, Y, show Finset.Icc 1 3 = {1,2,3} by decide, hu.1, hu.2.1, hu.2.2]
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := (h 3 (by norm_num)).2 0 1 (by norm_num)
  change 0 ≤ (-1:ℝ)^0 * iteratedDeriv 0
    (fun _ : ℝ => (-1:ℝ)^3 * D 3 (-1) (-1)) 1 at h0
  norm_num only [iteratedDeriv_zero, pow_zero, one_mul, pow_succ] at h0
  rw [D_three_neg_one] at h0
  nlinarith [mills_neg_one_pos]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by simpa [arena, actual, realize, claim] using result,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Analytic.XuYangMillsRemainder.Result.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.unit
  realizationName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.XuYangMillsRemainder.Result
    definition := some {
      owner := `D5.S3.Analytic.XuYangMillsRemainder.Result
      name := `D5.S3.Analytic.XuYangMillsRemainder.Result.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

namespace kernelIntegralIdentities
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ → ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ t p => J p t) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ t : ℝ,
    R.readout () t (fun v => 1 - v ^ 2 * t ^ 2 / 2) = exp (-t ^ 2 / 2) ∧
    R.readout () t (fun v => 1 - 3 * v ^ 2) =
      t ^ 2 / 2 * R.readout () t (fun v => v ^ 2 * (1 - v ^ 2))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := (h 0).1
  norm_num [rejected, realize] at h0
def family : Registration arena
    (type_of% @_root_.D5.S3.Analytic.XuYangMillsRemainder.Result.kernelIntegralIdentities) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.XuYangMillsRemainder.Result.kernelIntegralIdentities,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
    norm_num [actual, realize, J]

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Analytic.XuYangMillsRemainder.Result.kernelIntegralIdentities)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.kernelIntegralIdentities.unit
  realizationName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.kernelIntegralIdentities.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ t p => J p t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.XuYangMillsRemainder.Result
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }, {
      path := #["body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }, {
      path := #["body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end kernelIntegralIdentities

namespace gaussianLaplaceDerivative
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ t => exp t) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (x : ℝ), 0 < x →
    IntegrableOn (fun t : ℝ => R.readout () () (-x * t) *
      (-t * R.readout () () (-t ^ 2 / 2))) (Ioi 0) ∧
    (∫ t in Ioi (0 : ℝ), R.readout () () (-x * t) *
      (-t * R.readout () () (-t ^ 2 / 2))) =
      x * (∫ t in Ioi (0 : ℝ), R.readout () () (-x * t) *
        R.readout () () (-t ^ 2 / 2)) - 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := (h 1 (by norm_num)).2
  norm_num [rejected, realize] at h0
def family : Registration arena
    (type_of% @_root_.D5.S3.Analytic.XuYangMillsRemainder.Result.gaussianLaplaceDerivative) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.XuYangMillsRemainder.Result.gaussianLaplaceDerivative,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change exp (0 : ℝ) ≠ exp 1
    rw [exp_zero]
    exact ne_of_lt (one_lt_exp_iff.mpr zero_lt_one)

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Analytic.XuYangMillsRemainder.Result.gaussianLaplaceDerivative)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.gaussianLaplaceDerivative.unit
  realizationName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.gaussianLaplaceDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => exp t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.XuYangMillsRemainder.Result
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end gaussianLaplaceDerivative

end
end Reg.D5.S3.Analytic.XuYangMillsRemainder.Result
