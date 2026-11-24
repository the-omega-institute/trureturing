import D5.S3.Combinatorics.Geometry.Permutohedra.FaceFlags
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Counting proper prefix ranks from the ambient dimension. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Geometry.Permutohedra.FaceFlags

open _root_.D5.S3.Combinatorics.Graph.PrefixHamming
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (sensitivity)
open LeanInformationAudit

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

private def actual : Realization signature :=
  realize signature (fun _ _ n => n - 1) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, Fintype.card (Rank n) = R.readout () () n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  exact (by decide : Fintype.card (Rank 2) ≠ 0) (law (n := 2))

def evidence : Registration arena (type_of% (@Rossi.card_rank_type)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Rossi.card_rank_type, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    exact ⟨(), 1, 2, by decide⟩

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@Rossi.card_rank_type) (Realization signature) Unit Unit where
  unitName := `Rossi.card_rank_type.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.Permutohedra.FaceFlags.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => n - 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.Permutohedra.FaceFlags
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

end Reg.D5.S3.Combinatorics.Geometry.Permutohedra.FaceFlags
