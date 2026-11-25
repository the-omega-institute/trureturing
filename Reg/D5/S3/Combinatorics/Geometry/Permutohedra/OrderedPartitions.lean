import D5.S3.Combinatorics.Geometry.Permutohedra.OrderedPartitions
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Reading the number of blocks of an ordered partition. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OrderedPartitions

open _root_.Rossi
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (sensitivity)
open LeanInformationAudit

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ OrderedPartition (fun _ => ℕ)

private def actual : Realization signature :=
  realize signature (fun _ _ p => p.separators + 1) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (p : OrderedPartition n), rank (p.toCuts : Face n) = (n : ℤ) - (R.readout () n p : ℤ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let p : OrderedPartition 1 := ⟨0, fun _ => 0, fun a => ⟨0, by apply Fin.ext; have := a.isLt; omega⟩⟩
  have h := law p
  rw [p.rank_toCuts] at h
  change (1 : ℤ) - 1 = 1 - 0 at h
  omega

def evidence : Registration arena (type_of% (@Rossi.OrderedPartition.rank_toCuts)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Rossi.OrderedPartition.rank_toCuts, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    let twoBlocks : OrderedPartition 2 := ⟨1, id, Function.surjective_id⟩
    let oneBlock : OrderedPartition 2 := ⟨0, fun _ => 0, fun a => ⟨0, by apply Fin.ext; have := a.isLt; omega⟩⟩
    exact ⟨2, oneBlock, twoBlocks, by decide⟩

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@Rossi.OrderedPartition.rank_toCuts) (Realization signature) Unit Unit where
  unitName := `Rossi.OrderedPartition.rank_toCuts.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OrderedPartitions.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p.separators + 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.Permutohedra.OrderedPartitions
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OrderedPartitions
