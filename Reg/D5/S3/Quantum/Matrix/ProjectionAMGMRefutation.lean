import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.ProjectionAMGMRefutation
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Matrix.ProjectionAMGMRefutation
open _root_.D5.S3.Quantum.Matrix.ProjectionAMGMRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe whether the finite permutation set is the full universe. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Finset (Equiv.Perm (Fin 3))) (fun _ => Bool)

def actual : Realization signature :=
  realize signature
    (fun _ _ s => decide (s = Finset.univ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

/-- The observation at the exact source operand retains the complete equality. -/
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () sixPerms = true

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact Bool.noConfusion h

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), Finset.univ, ∅, ?_⟩
  have hne : (∅ : Finset (Equiv.Perm (Fin 3))) ≠ Finset.univ := by
    intro h
    have hm : (1 : Equiv.Perm (Fin 3)) ∈ (∅ : Finset (Equiv.Perm (Fin 3))) := by
      rw [h]
      exact Finset.mem_univ _
    exact Finset.notMem_empty _ hm
  simp [actual, realize, hne]

def source_registration : Registration arena (type_of% @sixPerms_univ) where
  actual := actual
  bridge := by simp [actual, realize]
  variation := ⟨by simpa [actual, realize] using sixPerms_univ, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sixPerms_univ) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.ProjectionAMGMRefutation.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.ProjectionAMGMRefutation.source_registration
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
    (fun _ _ s => decide (s = Finset.univ))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.ProjectionAMGMRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Matrix.ProjectionAMGMRefutation
