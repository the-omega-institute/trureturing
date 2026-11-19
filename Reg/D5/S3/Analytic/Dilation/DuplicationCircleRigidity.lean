import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Dilation.DuplicationCircleRigidity
import Reg.Support.SingleDependentReadout

/-! The cosine readout is determined by the circle's duplication law and unit fibre. -/

namespace Reg.D5.S3.Analytic.Dilation.DuplicationCircleRigidity

open _root_.D5.S3.Analytic.Dilation.DuplicationCircleRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => Real.cos t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev circleArena : Arena where
  signature := signature
  Law R := ∀ {p : ℝ → ℝ},
    Continuous p → Function.Periodic p (2 * Real.pi) →
    (∀ t, p (-t) = p t) → (∀ t, |p t| ≤ 1) →
    (∀ t, p (2 * t) = 2 * (p t) ^ 2 - 1) →
    (∀ t, p t = 1 ↔ ∃ k : ℤ, t = 2 * Real.pi * (k : ℝ)) →
    p = R.readout () ()

private theorem circle_rejected : ¬ circleArena.Law rejected := by
  intro h
  have hfibre (t : ℝ) : Real.cos t = 1 ↔ ∃ k : ℤ, t = 2 * Real.pi * (k : ℝ) := by
    simpa only [mul_comm (2 * Real.pi), eq_comm] using Real.cos_eq_one_iff t
  have he := h (p := Real.cos) Real.continuous_cos Real.cos_periodic Real.cos_neg
    Real.abs_cos_le_one Real.cos_two_mul hfibre
  have hv := congrFun he 0
  norm_num [rejected, realize] at hv

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, Real.pi, ?_⟩
  change Real.cos 0 ≠ Real.cos Real.pi
  norm_num

def circleFamily : Registration circleArena (type_of% @eq_cos_of_circle_duplication) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eq_cos_of_circle_duplication, rejected, circle_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    circleArena.Law actual rejected circle_rejected
  dependence := dependence

def circleAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eq_cos_of_circle_duplication) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Analytic.Dilation.DuplicationCircleRigidity.circleUnit
  realizationName := `Reg.D5.S3.Analytic.Dilation.DuplicationCircleRigidity.circleFamily
  realizationSource := none
  generated := false
  arena := .source ⟨circleArena⟩
  objectArena := .source ⟨circleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source circleArena ⟨circleFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => Real.cos t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Analytic.Dilation.DuplicationCircleRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.Dilation.DuplicationCircleRigidity
