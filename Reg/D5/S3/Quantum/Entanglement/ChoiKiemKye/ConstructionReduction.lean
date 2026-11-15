import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.BlockRank

open _root_.D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Blocks (rank_block)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u v
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type v} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (M : ∀ i, Matrix (κ i) (κ i) ℂ),
    r.readout () () (Matrix.blockDiagonal' M).rank (∑ i, (M i).rank)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (ι := PEmpty) (κ := fun _ => PEmpty) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def source_registration : Registration arena (type_of% @rank_block.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rank_block.{u, v}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rank_block.{u, v}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.BlockRank.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.BlockRank.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.BlockRank
