import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the binary-convolution bias identity. -/

namespace Reg.D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining
open _root_.D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p q => bconv p q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ p q : ℝ, 1 - 2 * R.readout () p q = (1 - 2 * p) * (1 - 2 * q)

abbrev sourceScope := type_of% (@bconv_bias)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0 0
  norm_num [rejected, realize] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨0, 0, 1, by norm_num [actual, realize, bconv]⟩

def source_registration : Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bconv_bias, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining.bconv_bias)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining.unit
  realizationName := `Reg.D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p q => bconv p q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining
