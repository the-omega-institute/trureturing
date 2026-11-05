import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of the faithful qutrit state's trace and positivity. -/

namespace Reg.D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation

open _root_.D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Rho0Trace

/-- Observe the trace of a qutrit matrix. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Matrix (Fin 3) (Fin 3) ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ M => Matrix.trace M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () rho0 = 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change (0 : ℂ) = 1 at h
  exact zero_ne_one h

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change Matrix.trace (0 : Matrix (Fin 3) (Fin 3) ℂ) ≠
    Matrix.trace (1 : Matrix (Fin 3) (Fin 3) ℂ)
  norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

def source_registration : Registration arena (type_of% @rho0_trace) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rho0_trace, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rho0_trace) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation.Rho0Trace.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation.Rho0Trace.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ M => Matrix.trace M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Rho0Trace

namespace Rho0PosDef

/-- Observe positive definiteness of a qutrit matrix. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Matrix (Fin 3) (Fin 3) ℂ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ M => @decide M.PosDef (Classical.propDecidable _))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () rho0 = true

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change false = true at h
  exact Bool.false_ne_true h

private theorem zero_not_posDef : ¬ (0 : Matrix (Fin 3) (Fin 3) ℂ).PosDef := by
  intro h
  have hzero := h.diag_pos (i := 0)
  simp at hzero

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change @decide (0 : Matrix (Fin 3) (Fin 3) ℂ).PosDef (Classical.propDecidable _) ≠
    @decide (1 : Matrix (Fin 3) (Fin 3) ℂ).PosDef (Classical.propDecidable _)
  simp [zero_not_posDef, Matrix.PosDef.one]

def source_registration : Registration arena (type_of% @rho0_posDef) where
  actual := actual
  bridge := by simp [actual, realize]
  variation := ⟨by simpa [actual, realize] using rho0_posDef, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rho0_posDef) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation.Rho0PosDef.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation.Rho0PosDef.source_registration
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
    owner := `D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation
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

end Rho0PosDef

end
end Reg.D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation
