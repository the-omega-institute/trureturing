import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumChannels.ContractionGeometry.NorthPoleBallCriterion
import Reg.Support.SingleDependentReadout

/-! Source-bound axial-coordinate audit of the exact whole-ball criterion. -/

namespace Reg.D5.S3.QuantumChannels.ContractionGeometry.NorthPoleBallCriterion

open _root_.D5.S3.QuantumChannels.ContractionGeometry.NorthPoleBallCriterion
open _root_.D5.S3.QuantumChannels.AmplitudeDampingContraction (dampedAxis)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the actual axial coordinate over every real axial parameter and height. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ a z => dampedAxis (1 - a) z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- All transverse coordinates, source-ball hypotheses and both axial endpoints remain in scope. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a lambda : ℝ), 0 ≤ a → a ≤ 1 →
    ((∀ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 ≤ 1 →
      (lambda * x) ^ 2 + (lambda * y) ^ 2 + (R.readout () a z) ^ 2 ≤ 1) ↔
      lambda ^ 2 ≤ a)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 0 1 (by norm_num) (by norm_num)).mp (by
    intro x y z hin
    change (1 * x) ^ 2 + (1 * y) ^ 2 + (0 : ℝ) ^ 2 ≤ 1
    nlinarith only [hin, sq_nonneg z])
  norm_num at hbad

def source_registration : Registration arena (type_of% @north_pole_ball_preserving_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨north_pole_ball_preserving_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := by
    intro i
    exact ⟨1, 0, 1, by norm_num [actual, realize, dampedAxis]⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@north_pole_ball_preserving_iff) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.QuantumChannels.ContractionGeometry.NorthPoleBallCriterion.unit
  realizationName :=
    `Reg.D5.S3.QuantumChannels.ContractionGeometry.NorthPoleBallCriterion.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a z => dampedAxis (1 - a) z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.QuantumChannels.ContractionGeometry.NorthPoleBallCriterion
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg",
        "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumChannels.ContractionGeometry.NorthPoleBallCriterion
