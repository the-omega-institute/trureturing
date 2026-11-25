import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.SharpBorn
import Reg.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.FourierFiveThreshold
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.SharpBorn

open _root_.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    CoordinateFive (fun _ => CoordinateFive) (fun _ => ℝ)

private def actual : Realization signature :=
  realize signature (fun _ x y => positiveFourierScore x y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 4) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x y : CoordinateFive), ‖x‖ = 1 → ‖y‖ = 1 →
    R.readout () x y ≤ (14 + 2 * Real.sqrt 5) / 5

private theorem rejected_law : ¬ arena.Law rejected := by
  let x : CoordinateFive := coordinateBasisFive 0
  have hx : ‖x‖ = 1 := coordinateBasisFive.orthonormal.norm_eq_one 0
  intro h
  have hbad := h x x hx hx
  change (4 : ℝ) ≤ (14 + 2 * Real.sqrt 5) / 5 at hbad
  linarith only [hbad, sharp_sqrt_five_bounds.2]

private theorem dependence : ObservationalDependence signature actual :=
  _root_.Reg.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.FourierFiveThreshold.sourceRegistration.dependence

def sourceRegistration :
    Registration arena (type_of% @positiveFourierScore_le_sharp) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positiveFourierScore_le_sharp, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

/-- The observed quantity is the exact two-basis score in the sharp all-unit theorem. -/
def sharpRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@positiveFourierScore_le_sharp) (Realization signature) Unit Unit := {
  unitName := .str ``sourceRegistration "unit"
  realizationName := ``sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x y => positiveFourierScore x y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.SharpBorn
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.SharpBorn
