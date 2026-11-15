import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor
import D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
import Reg.Support.SingleDependentReadout
import Mathlib.Algebra.Field.ULift

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Reuse

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
open Module Matrix

universe u v w

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  omega

namespace Rectangle

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {K : Type u} {E : Type v} {F : Type w}
    [Field K] [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
    [FiniteDimensional K E] [FiniteDimensional K F]
    (U : Submodule K E) (V : Submodule K F),
    R.readout () () (finrank K ↥(rectangle U V)) (finrank K U * finrank K V)

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  exact @h (ULift.{u} ℚ) PUnit.{v+1} PUnit.{w+1}
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance ⊥ ⊥

def source_registration : Registration arena.{u,v,w} (type_of% @rectangle_finrank) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rectangle_finrank, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@rectangle_finrank) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor.rectangle_finrank.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Reuse.Rectangle.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
      "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Rectangle

namespace PencilRank

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x y : ℕ), y ≤ x → R.readout () () (pencil x y).rank ((x + 1) * y)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 (by decide)

def source_registration : Registration arena (type_of% @pencil_rank_of_ge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pencil_rank_of_ge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@pencil_rank_of_ge) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.pencil_rank_of_ge.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Reuse.PencilRank.source_registration
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
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end PencilRank

end Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Reuse
