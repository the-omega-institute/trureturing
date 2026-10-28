import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.LiteralLeadingCertificates
import Reg.Support.SingleDependentReadout
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.LiteralLeadingCertificates
open _root_.D5.S3.Observer.CubicGain.LiteralLeadingCertificates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℤ) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ _ z => decide (z ≠ 0)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () topR1.det = true ∧ R.readout () () topR2.det = true ∧
    R.readout () () topA.det = true ∧ R.readout () () topC.det = true
private theorem rejected_law : ¬ arena.Law rejected := by simp [arena, rejected, realize]
private theorem actual_law : arena.Law actual := by
  simpa [arena, actual, realize] using leading_determinants_ne_zero
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by decide +kernel⟩
def source_registration : Registration arena (type_of% @leading_determinants_ne_zero) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@leading_determinants_ne_zero) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.LiteralLeadingCertificates.leading_determinants_ne_zero.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.LiteralLeadingCertificates.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => decide (z ≠ 0)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.LiteralLeadingCertificates
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["fn","arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["fn","arg"]
        booleanPredicate := true },
      { path := #["arg","fn","arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["fn","arg"]
        booleanPredicate := true },
      { path := #["arg","arg","fn","arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["fn","arg"]
        booleanPredicate := true },
      { path := #["arg","arg","arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["fn","arg"]
        booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Reg.D5.S3.Observer.CubicGain.LiteralLeadingCertificates
