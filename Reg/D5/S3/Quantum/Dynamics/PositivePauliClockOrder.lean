import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.PositivePauliClockOrder
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of controlled unitarity and structure-state positivity. -/

namespace Reg.D5.S3.Quantum.Dynamics.PositivePauliClockOrder

open _root_.D5.S3.Quantum.Dynamics.PositivePauliClockOrder
open _root_.D5.S3.Quantum.FiniteDimensional
open _root_.D5.S3.Quantum.EnvironmentRecords
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace ControlledUnitary

/-- Observe the controlled matrix at its two source blocks. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature QubitMatrix
    (fun _ => QubitMatrix) (fun _ => JointQubitEnvironmentMatrix)

def actual : Realization signature :=
  realize signature (fun _ Q P => controlled Q P) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (Q P : QubitMatrix),
    Q ∈ unitary QubitMatrix → P ∈ unitary QubitMatrix →
    R.readout () Q P ∈ unitary JointQubitEnvironmentMatrix

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h 1 1 (by simp) (by simp)
  change (0 : JointQubitEnvironmentMatrix) ∈ unitary JointQubitEnvironmentMatrix at hz
  simp only [Unitary.mem_iff, star_zero, zero_mul, zero_ne_one, false_and] at hz

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro h
  have he := congrArg (fun M : JointQubitEnvironmentMatrix => M (1, 0) (1, 0)) h
  change (0 : ℂ) = 1 at he
  exact zero_ne_one he

def source_registration : Registration arena (type_of% @controlled_unitary) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨controlled_unitary, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@controlled_unitary) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Dynamics.PositivePauliClockOrder.ControlledUnitary.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Dynamics.PositivePauliClockOrder.ControlledUnitary.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ Q P => controlled Q P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.PositivePauliClockOrder
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end ControlledUnitary

namespace SigmaPosDef

open scoped ComplexOrder MatrixOrder

/-- Observe positive definiteness of a qubit matrix. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => QubitMatrix) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ M => @decide M.PosDef (Classical.propDecidable _))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () sigma = true

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change false = true at h
  exact Bool.false_ne_true h

private theorem zero_not_posDef : ¬ (0 : QubitMatrix).PosDef := by
  intro h
  have hzero := h.diag_pos (i := 0)
  simp at hzero

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change @decide (0 : QubitMatrix).PosDef (Classical.propDecidable _) ≠
    @decide (1 : QubitMatrix).PosDef (Classical.propDecidable _)
  simp [zero_not_posDef, Matrix.PosDef.one]

def source_registration : Registration arena (type_of% @sigma_posDef) where
  actual := actual
  bridge := by simp [actual, realize]
  variation := ⟨by simpa [actual, realize] using sigma_posDef, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sigma_posDef) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Dynamics.PositivePauliClockOrder.SigmaPosDef.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Dynamics.PositivePauliClockOrder.SigmaPosDef.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ M => @decide M.PosDef (Classical.propDecidable _))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.PositivePauliClockOrder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end SigmaPosDef

end
end Reg.D5.S3.Quantum.Dynamics.PositivePauliClockOrder
