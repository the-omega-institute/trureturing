import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumBounds.RebitExclusionDistance
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.QuantumBounds.RebitExclusionDistance
open _root_.D5.S3.QuantumBounds.RebitExclusionDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the least-value ratio at its denominator coordinate. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ n => 1 / n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete attainable-distance set and observe only its asserted least value. -/
abbrev arena : Arena where
  signature := signature
  Law R := IsLeast {d : ℝ | ∃ ρ E, IsRebitStrategy ρ E ∧ d = dist ρ E}
    (R.readout () () 12)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbound := result.2 h.1
  change (1 / 12 : ℝ) ≤ 0 at hbound
  norm_num at hbound

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumBounds.RebitExclusionDistance.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumBounds.RebitExclusionDistance.unit
  realizationName := `Reg.D5.S3.QuantumBounds.RebitExclusionDistance.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => 1 / n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.RebitExclusionDistance
    definition := some {
      owner := `D5.S3.QuantumBounds.RebitExclusionDistance
      name := `D5.S3.QuantumBounds.RebitExclusionDistance.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms signature
#print axioms actual
#print axioms rejected
#print axioms arena
#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumBounds.RebitExclusionDistance
