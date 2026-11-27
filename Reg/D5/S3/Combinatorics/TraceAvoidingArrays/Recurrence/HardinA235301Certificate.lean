import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Certificate
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound readout of the stored initial transfer histories. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Certificate

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Certificate
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer (Hist State path)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace InitialPath

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 10) (fun _ => Hist State)

private def actual : Realization signature :=
  realize signature (fun _ _ i => initialPath i) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ i : Fin 10, path (i.val + 1) = R.readout () () i

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h : path ((0 : Fin 10).val + 1) = [] := law 0
  rw [initial_path_eq] at h
  exact (by decide +kernel : initialPath 0 ≠ []) h

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  exact ⟨(), 0, 1, (by decide +kernel : initialPath 0 ≠ initialPath 1)⟩

def family : Registration arena (type_of% @initial_path_eq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨initial_path_eq, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@initial_path_eq) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Certificate.InitialPath.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Certificate.InitialPath.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => initialPath i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Certificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end InitialPath

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Certificate
