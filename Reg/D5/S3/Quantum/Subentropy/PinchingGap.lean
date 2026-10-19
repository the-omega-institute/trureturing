import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Subentropy.PinchingGap
import Reg.Support.SingleDependentReadout

/-! Full-source registration for the actual subentropy pinching-gap laws. -/

noncomputable section
set_option autoImplicit false
namespace Reg.D5.S3.Quantum.Subentropy.PinchingGap
open _root_.D5.S3.Quantum.Subentropy.PinchingGap
open _root_.D5.S3.Quantum.Subentropy
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u v

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} {B : Type v} [Fintype X] [DecidableEq X]
    [Fintype B] [DecidableEq B] (i₀ : X × B),
    ConvexOn ℝ {A : Matrix (X × B) (X × B) ℂ | A.PosSemidef ∧ A.trace = 1}
      (fun A => Basic.matrixSubentropy (ClassicalQuantumGram.blockPinch A) - Basic.matrixSubentropy A) ∧
    ∀ A : Matrix (X × B) (X × B) ℂ, A.PosSemidef → A.trace = 1 →
      R.readout () () 0
        (Basic.matrixSubentropy (ClassicalQuantumGram.blockPinch A) - Basic.matrixSubentropy A)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let i₀ : ULift.{u} Unit × ULift.{v} Unit := ⟨⟨()⟩, ⟨()⟩⟩
  have hp : Matrix.PosSemidef (1 : Matrix (ULift.{u} Unit × ULift.{v} Unit)
      (ULift.{u} Unit × ULift.{v} Unit) ℂ) := Matrix.PosSemidef.one
  have ht : (1 : Matrix (ULift.{u} Unit × ULift.{v} Unit)
      (ULift.{u} Unit × ULift.{v} Unit) ℂ).trace = 1 := by simp [Matrix.trace]
  have he := (h i₀).2 1 hp ht
  exact he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hbad : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) le_rfl
  norm_num at hbad

def source_registration : Registration arena.{u,v} (type_of% @actual_pinching_gap_laws.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_pinching_gap_laws, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_pinching_gap_laws.{u,v}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Subentropy.PinchingGap.actual_pinching_gap_laws.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.PinchingGap.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.PinchingGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

namespace Concavity
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (i₀ : ι),
    Convex ℝ {A : Matrix ι ι ℂ | A.PosSemidef ∧ A.trace = 1} ∧
    ∀ ⦃A : Matrix ι ι ℂ⦄, A.PosSemidef ∧ A.trace = 1 →
    ∀ ⦃C : Matrix ι ι ℂ⦄, C.PosSemidef ∧ C.trace = 1 →
    ∀ ⦃c d : ℝ⦄, 0 ≤ c → 0 ≤ d → c + d = 1 →
      R.readout () () (c • Basic.matrixSubentropy A + d • Basic.matrixSubentropy C)
        (Basic.matrixSubentropy (c • A + d • C))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let i₀ : ULift.{u} Unit := ⟨()⟩
  have hd : (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ).PosSemidef ∧
      (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ).trace = 1 :=
    ⟨Matrix.PosSemidef.one, by simp [Matrix.trace]⟩
  exact (h i₀).2 (A := 1) hd (C := 1) hd (c := 1) (d := 0)
    zero_le_one le_rfl (by norm_num)

def source_registration : Registration arena.{u} (type_of% @matrix_subentropy_concave.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@matrix_subentropy_concave, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
end Concavity

def concavity_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@matrix_subentropy_concave.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Subentropy.PinchingGap.matrix_subentropy_concave.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.PinchingGap.Concavity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Concavity.arena⟩
  objectArena := .source ⟨Concavity.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Concavity.arena ⟨Concavity.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.PinchingGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


end Reg.D5.S3.Quantum.Subentropy.PinchingGap
