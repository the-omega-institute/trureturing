import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the normalized Walsh matrix's unitarity. -/

namespace Reg.D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation

open _root_.D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the source membership predicate as its matrix operand varies. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Matrix (Fin 4) (Fin 4) ℂ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature
    (fun _ _ U => @decide (U ∈ Matrix.unitaryGroup (Fin 4) ℂ) (Classical.propDecidable _))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

/-- Retain the complete unitarity assertion at the published Walsh matrix. -/
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () u4 = true

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact Bool.false_ne_true h

theorem zero_not_unitary :
    (0 : Matrix (Fin 4) (Fin 4) ℂ) ∉ Matrix.unitaryGroup (Fin 4) ℂ := by
  intro hz
  have hentry := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0)
    (Matrix.mem_unitaryGroup_iff.mp hz)
  norm_num at hentry

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  simp [actual, realize, zero_not_unitary]

def source_registration : Registration arena (type_of% u4_unitary) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using u4_unitary,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation.u4_unitary)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation.source_registration
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
    (fun _ _ U => @decide (U ∈ Matrix.unitaryGroup (Fin 4) ℂ) (Classical.propDecidable _))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation
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

set_option pp.proofs false in
#print _root_.D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation.u4_unitary
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation
