import D5.S1.Recurrence.Periodic.EulerDivisorPropagation
import D5.S1.Recurrence.Periodic.EulerTwoPrimary
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound dependent-family audits of the two complete source assertions. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S1.Recurrence.Periodic.EulerDivisorPropagation
open _root_.D5.S1.Recurrence.Periodic.EulerUpDownSource
open _root_.D5.S1.Recurrence.Periodic.EulerSecantBridge
open _root_.D5.S1.Recurrence.Periodic.EulerDivisorPropagation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature := realize signature (fun _ _ n => E n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => if n = 0 then 3 else 1) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 3, ?_⟩
  change E 0 ≠ E 3
  rw [boundary_values.1, boundary_values.2.2.2.1]
  decide

namespace divisor_propagation
abbrev arena : Arena where
  signature := signature
  Law r := ∀ k m d : ℕ, 2 < d → d ∣ r.readout () () k → d ∣ r.readout () () (k + m * Nat.totient d)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 1 3 (by decide) (by change 3 ∣ 3; decide)
  change 3 ∣ 1 at hh
  norm_num at hh
def family : Registration arena (type_of% (@divisor_propagation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@divisor_propagation, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@divisor_propagation) (Realization signature) Unit Unit := {
  unitName := `D5.S1.Recurrence.Periodic.EulerDivisorPropagation.divisor_propagation.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Periodic.EulerDivisorPropagation.divisor_propagation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => E n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Periodic.EulerDivisorPropagation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms registration
end divisor_propagation

namespace particular
abbrev arena : Arena where
  signature := signature
  Law r := ∀ k m : ℕ, k ≠ 3 → r.readout () () k ∣ r.readout () () (k + m * Nat.totient (r.readout () () k))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 1 (by decide)
  change 3 ∣ 1 at hh
  norm_num at hh
def family : Registration arena (type_of% (@particular)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@particular, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@particular) (Realization signature) Unit Unit := {
  unitName := `D5.S1.Recurrence.Periodic.EulerDivisorPropagation.particular.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Periodic.EulerDivisorPropagation.particular.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => E n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Periodic.EulerDivisorPropagation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms registration
end particular

end Reg.D5.S1.Recurrence.Periodic.EulerDivisorPropagation
