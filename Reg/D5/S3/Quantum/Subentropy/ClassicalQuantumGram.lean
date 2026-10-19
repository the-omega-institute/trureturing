import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Subentropy.ClassicalQuantumGram
import Reg.Support.SingleDependentReadout

noncomputable section
set_option autoImplicit false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Information.OrthogonalRecordEntropy
open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Subentropy.ClassicalQuantumGram
universe u v

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ q r => q = r) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ q r => q + 1 = r) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} {B : Type v} [Fintype X] [DecidableEq X]
    [Fintype B] [DecidableEq B] (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B),
    R.readout () () (conditionalSubentropy p hp hs ρ)
      (matrixSubentropy (blockPinch ((cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ)) -
      matrixSubentropy ((cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ))
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let ρ : ULift.{u} Unit → DensityState (ULift.{v} Unit) := fun _ => pointerState ⟨()⟩
  have hb := @h (ULift.{u} Unit) (ULift.{v} Unit) inferInstance inferInstance
    inferInstance inferInstance (fun _ => 1) (fun _ => by norm_num) (by simp) ρ
  have ha := cq_conditional_eq_pinchingGap (fun _ : ULift.{u} Unit => 1)
    (fun _ => by norm_num) (by simp) ρ
  simp only [rejected, realize] at hb
  linarith
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have ht := congrFun he 0
  norm_num [actual, realize] at ht
def family : Registration arena.{u,v} (type_of% @cq_conditional_eq_pinchingGap.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cq_conditional_eq_pinchingGap, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cq_conditional_eq_pinchingGap.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.ClassicalQuantumGram.cq_conditional_eq_pinchingGap.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.ClassicalQuantumGram.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q r => q = r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.ClassicalQuantumGram
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Pure
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} {B : Type v} [Fintype X] [DecidableEq X]
    [Fintype B] [DecidableEq B] (w : (X × B) → ℂ)
    (hw : ∑ i, star (w i) * w i = 1),
    matrixSubentropy (blockPinch (Matrix.vecMulVec w (star w))) -
      matrixSubentropy (Matrix.vecMulVec w (star w)) =
      matrixSubentropy (Matrix.diagonal
        (fun x => ((∑ b, Complex.normSq (w (x,b)) : ℝ) : ℂ))) ∧
    ∀ x : X, R.readout () ()
      (matrixSubentropy (blockPinch (Matrix.vecMulVec w (star w))) -
        matrixSubentropy (Matrix.vecMulVec w (star w)))
      (1 - ∑ b, Complex.normSq (w (x,b)))
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hb := @h (ULift.{u} Unit) (ULift.{v} Unit) inferInstance inferInstance
    inferInstance inferInstance (fun _ => 1) (by simp)
  exact hb.2 ⟨()⟩
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have ht := congrFun he 0
  norm_num [actual, realize] at ht
def family : Registration arena.{u,v} (type_of% @pure_block_pinching.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pure_block_pinching, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pure_block_pinching.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.ClassicalQuantumGram.pure_block_pinching.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.ClassicalQuantumGram.Pure.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.ClassicalQuantumGram
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Pure

namespace Row
abbrev signature : Signature where
  Params := Type v
  State B := Matrix B B ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ B := Matrix B B ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{v} :=
  realize signature (fun _ _ A C => A = C) (fun e => nomatch e)
def rejected : Realization signature.{v} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{v}
  Law R := ∀ {X : Type u} {B : Type v} [Fintype X] [DecidableEq X]
    [Fintype B] [DecidableEq B] (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ρ : X → DensityState B),
    R.readout () B (cqRowSqrt p ρ * (cqRowSqrt p ρ).conjTranspose)
      (∑ x, p x • CStarMatrix.ofMatrix.symm (ρ x).1)
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact @h (ULift.{u} Unit) (ULift.{v} Unit) inferInstance inferInstance
    inferInstance inferInstance (fun _ => 1) (fun _ => by norm_num)
    (fun _ => pointerState ⟨()⟩)
private theorem dependence : ObservationalDependence signature.{v} actual := by
  intro i
  refine ⟨ULift.{v} Unit, 0, 1, ?_⟩
  intro he
  have ht := congrFun he 0
  have hz : (0 : Matrix (ULift.{v} Unit) (ULift.{v} Unit) ℂ) = 0 := rfl
  have ho : (1 : Matrix (ULift.{v} Unit) (ULift.{v} Unit) ℂ) = 0 :=
    (show (0 : Matrix (ULift.{v} Unit) (ULift.{v} Unit) ℂ) = 0 ↔
      (1 : Matrix (ULift.{v} Unit) (ULift.{v} Unit) ℂ) = 0 from iff_of_eq ht).mp hz
  have hc := congrArg (fun A : Matrix (ULift.{v} Unit) (ULift.{v} Unit) ℂ => A ⟨()⟩ ⟨()⟩) ho
  norm_num at hc
def family : Registration arena.{u,v} (type_of% @row_mul_adjoint.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@row_mul_adjoint, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence
def audit.{u_1, u_2} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@row_mul_adjoint.{u_1,u_2}) (Realization signature.{u_2}) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.ClassicalQuantumGram.row_mul_adjoint.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.ClassicalQuantumGram.Row.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A C => A = C) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.ClassicalQuantumGram
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Row

end Reg.D5.S3.Quantum.Subentropy.ClassicalQuantumGram
