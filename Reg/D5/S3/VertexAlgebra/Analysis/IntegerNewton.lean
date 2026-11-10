import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import Mathlib.Algebra.Field.ULift
import D5.S3.VertexAlgebra.Analysis.IntegerNewton
/-! Full-telescope source realizations and single-readout sensitivity evidence. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Function LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.Analysis.IntegerNewton
open _root_.D5.S3.VertexAlgebra.FieldNormalProductLocality (delta)
universe u
namespace Reg.D5.S3.VertexAlgebra.Analysis.IntegerNewton
abbrev equalitySignature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature (Type u) (fun V => V) (fun V => V → Prop)
def equalityActual : Realization equalitySignature.{u} :=
  realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e)
def equalityRejected : Realization equalitySignature.{u} :=
  realize equalitySignature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem equality_dependence :
    ObservationalDependence equalitySignature.{u} equalityActual := by
  intro i
  refine ⟨ULift.{u} Bool, ⟨false⟩, ⟨true⟩, ?_⟩
  intro h
  have hh := congrFun h (⟨false⟩ : ULift.{u} Bool)
  have hz : (⟨true⟩ : ULift.{u} Bool) = ⟨false⟩ := Eq.mp hh rfl
  cases hz

namespace newton
def arena : Arena where
  signature := equalitySignature.{u}
  Law R := ∀ {V : Type u} [AddCommGroup V] (q : ℤ → V) (N : ℕ),
    (fwdDiff (1 : ℤ))^[N] q = 0 → ∀ m : ℤ,
      R.readout () V (q m)
        (∑ j ∈ range N, (Ring.choose m j : ℤ) • ((fwdDiff (1 : ℤ))^[j] q) 0)
private theorem rejected_bad : ¬ arena.{u}.Law equalityRejected := by
  intro h
  exact h (V := ULift.{u} ℤ) (fun _ => 0) 0 rfl 0
def evidence : Registration arena (type_of% (@int_newton_of_fwdDiff_iter_eq_zero.{u})) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@int_newton_of_fwdDiff_iter_eq_zero.{u}, equalityRejected, rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law equalityActual equalityRejected rejected_bad
  dependence := equality_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@int_newton_of_fwdDiff_iter_eq_zero.{u}) (Realization equalitySignature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.IntegerNewton.newton.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.IntegerNewton.newton.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize equalitySignature.{u} equalityActual.{u}.readout equalityActual.{u}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.IntegerNewton
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end newton

namespace delta
def arena : Arena where
  signature := equalitySignature.{u}
  Law R := ∀ {V : Type u} [AddCommGroup V] (C : ℤ → ℤ → V) (N : ℕ),
    delta^[N] C = 0 → ∀ m n : ℤ,
      R.readout () V (C m n)
        (∑ j ∈ range N, (Ring.choose m j : ℤ) • contactCoefficient C j (m+n))
private theorem rejected_bad : ¬ arena.{u}.Law equalityRejected := by
  intro h
  exact h (V := ULift.{u} ℤ) (fun _ _ => 0) 0 rfl 0 0
def evidence : Registration arena (type_of% (@delta_newton.{u})) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@delta_newton.{u}, equalityRejected, rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law equalityActual equalityRejected rejected_bad
  dependence := equality_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@delta_newton.{u}) (Realization equalitySignature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.IntegerNewton.delta.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.IntegerNewton.delta.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize equalitySignature.{u} equalityActual.{u}.readout equalityActual.{u}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.IntegerNewton
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end delta

namespace choose
def arena : Arena where
  signature := equalitySignature.{u}
  Law R := ∀ {K : Type u} [Field K] [CharZero K] (x : K) (j : ℕ),
    R.readout () K ((j+1 : K) * Ring.choose x (j+1)) ((x-j) * Ring.choose x j)
private theorem rejected_bad : ¬ arena.{u}.Law equalityRejected := by
  intro h
  letI : CharZero (ULift.{u} ℚ) := ⟨by
    intro m n hmn
    exact Nat.cast_injective (congrArg ULift.down hmn : (m : ℚ) = (n : ℚ))⟩
  exact h (K := ULift.{u} ℚ) 0 0
def evidence : Registration arena (type_of% (@choose_succ_mul.{u})) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@choose_succ_mul.{u}, equalityRejected, rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law equalityActual equalityRejected rejected_bad
  dependence := equality_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@choose_succ_mul.{u}) (Realization equalitySignature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.IntegerNewton.choose.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.IntegerNewton.choose.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize equalitySignature.{u} equalityActual.{u}.readout equalityActual.{u}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.IntegerNewton
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end choose

namespace norm
abbrev signature : Signature := _root_.Reg.Support.UniverseSingleReadout.signature
  Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 2) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (m : ℤ) (j : ℕ),
    R.readout () () ((Ring.choose m j : ℤ) : ℂ) ≤ (1+|(m : ℝ)|)^j
private theorem rejected_bad : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0
  change (2 : ℝ) ≤ 1 at hh
  norm_num at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
  norm_num
def evidence : Registration arena (type_of% (@norm_int_choose_le_pow)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨norm_int_choose_le_pow, rejected, rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_bad
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@norm_int_choose_le_pow) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.IntegerNewton.norm.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.IntegerNewton.norm.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.IntegerNewton
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end norm
end Reg.D5.S3.VertexAlgebra.Analysis.IntegerNewton
