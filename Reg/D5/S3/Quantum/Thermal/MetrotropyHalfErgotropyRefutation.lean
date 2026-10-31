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

/-- Read the row at a genuine index of the published Walsh table. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 4) (fun _ => Fin 4 → ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ i => u4 i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Reconstruct the full matrix from its rows and retain the original unitarity law. -/
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () ∈ Matrix.unitaryGroup (Fin 4) ℂ

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : (0 : Matrix (Fin 4) (Fin 4) ℂ) ∈ Matrix.unitaryGroup (Fin 4) ℂ := h
  have hentry := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0)
    (Matrix.mem_unitaryGroup_iff.mp hz)
  norm_num at hentry

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hentry := congrFun h 1
  norm_num [actual, realize, u4, Matrix.smul_apply, smul_eq_mul] at hentry

def source_registration : Registration arena (type_of% u4_unitary) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨u4_unitary, rejected, rejected_law⟩
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
  readout := some (realize signature (fun _ _ i => u4 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation.u4_unitary
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation
