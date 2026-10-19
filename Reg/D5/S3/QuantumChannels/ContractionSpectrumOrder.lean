import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumChannels.ContractionSpectrumOrder
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the inverse hyperbolic tangent derivative. -/

namespace Reg.D5.S3.QuantumChannels.ContractionSpectrumOrder
open _root_.D5.S3.QuantumChannels.ContractionSpectrumOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 1 / (1 - x ^ 2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x : ℝ}, x ∈ Set.Ioo (-1 : ℝ) 1 →
    HasDerivAt Real.artanh (R.readout () () x) x

abbrev sourceScope := type_of% (@hasDerivAt_artanh)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hd := h (x := 0) (by constructor <;> norm_num)
  have he := (hasDerivAt_artanh (x := 0) (by constructor <;> norm_num)).unique hd
  norm_num [rejected, realize] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1 / 2, by norm_num [actual, realize]⟩

def source_registration : Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_artanh, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumChannels.ContractionSpectrumOrder.hasDerivAt_artanh)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumChannels.ContractionSpectrumOrder.unit
  realizationName := `Reg.D5.S3.QuantumChannels.ContractionSpectrumOrder.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 1 / (1 - x ^ 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumChannels.ContractionSpectrumOrder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumChannels.ContractionSpectrumOrder
