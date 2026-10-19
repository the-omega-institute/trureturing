import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.LinGProperty.TraceDistanceBound
import Reg.Support.SingleDependentReadout

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped ComplexOrder
open _root_.D5.S3.Quantum.Matrix.LinGProperty
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Quantum.Matrix.LinGProperty.TraceDistanceBound
universe u
abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := Type u
  State n := Matrix n n ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ M => M.PosSemidef) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {A X B : Matrix n n ℂ}, (fromBlocks A X Xᴴ B).PosSemidef →
    A.trace = 1 → B.trace = 1 →
    R.readout () n
      ((((1-‖X.trace‖^2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) - (A-B)*(A-B))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hw : (fromBlocks (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) 0 0
      (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)).PosSemidef := by
    rw [Matrix.fromBlocks_one]
    exact Matrix.PosSemidef.one
  exact @h (ULift.{u} Unit) inferInstance inferInstance 1 0 1
    (by simpa using hw) (by simp [Matrix.trace]) (by simp [Matrix.trace])
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, 0, -1, ?_⟩
  intro he
  have hn : (- (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)).PosSemidef := by
    have hz : (0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ).PosSemidef := Matrix.PosSemidef.zero
    change ((0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ).PosSemidef) =
      ((-1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ).PosSemidef) at he
    exact he.mp hz
  have hh := hn.diag_nonneg (i := (⟨()⟩ : ULift.{u} Unit))
  norm_num at hh
def family : Registration arena.{u} (type_of% @normalized_difference_square_le.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalized_difference_square_le, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@normalized_difference_square_le.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.normalized_difference_square_le.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.TraceDistanceBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => M.PosSemidef) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.LinGProperty.TraceDistanceBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
namespace TraceNorm
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {A X B : Matrix n n ℂ}, (fromBlocks A X Xᴴ B).PosSemidef →
    A.trace = 1 → B.trace = 1 → R.readout () () ‖X.trace‖ 1
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hw : (fromBlocks (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) 0 0
      (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)).PosSemidef := by
    rw [Matrix.fromBlocks_one]
    exact Matrix.PosSemidef.one
  exact @h (ULift.{u} Unit) inferInstance inferInstance 1 0 1
    (by simpa using hw) (by simp [Matrix.trace]) (by simp [Matrix.trace])
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have ht := congrFun he 0
  norm_num [actual, realize] at ht
def family : Registration arena.{u} (type_of% @normalized_trace_norm_le_one.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalized_trace_norm_le_one, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@normalized_trace_norm_le_one.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.normalized_trace_norm_le_one.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.TraceDistanceBound.TraceNorm.family
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
    owner := `D5.S3.Quantum.Matrix.LinGProperty.TraceDistanceBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end TraceNorm

end Reg.D5.S3.Quantum.Matrix.LinGProperty.TraceDistanceBound
