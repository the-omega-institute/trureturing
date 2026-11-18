import D5.S3.Quantum.Matrix.HsfCubicRadial
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Scalar observations retain the complete source matrix telescopes. -/

set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder

namespace Reg.D5.S3.Quantum.Matrix.HsfCubicRadial
noncomputable section
universe u

private abbrev pairSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

namespace CubicExpansion
private def actual : Realization pairSignature :=
  realize pairSignature (fun _ _ x y => x = y) (fun e => nomatch e)
private def rejected : Realization pairSignature :=
  realize pairSignature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence pairSignature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hf : (1 : ℝ) = 0 := Eq.mp (congrFun h 0) rfl
  norm_num at hf
private abbrev arena : Arena where
  signature := pairSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (t : ℝ),
    R.readout () () (Matrix.trace ((A + t • B)^3)).re (
      (Matrix.trace (A^3)).re + 3*(Matrix.trace (A*A*B)).re*t +
      3*(Matrix.trace (A*B*B)).re*t^2 + (Matrix.trace (B^3)).re*t^3)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (n := ULift.{u} Unit) 0 0 0
private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfCubicRadial.trace_cubic.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨
    @_root_.D5.S3.Quantum.Matrix.HsfCubicRadial.trace_cubic.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfCubicRadial.trace_cubic.{u}) (Realization pairSignature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfCubicRadial.CubicExpansion.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfCubicRadial.CubicExpansion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.HsfCubicRadial
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CubicExpansion

namespace WeightedSquare
private def actual : Realization pairSignature :=
  realize pairSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
private def rejected : Realization pairSignature :=
  realize pairSignature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence pairSignature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) le_rfl
  norm_num at hf
private abbrev arena : Arena where
  signature := pairSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (W E : Matrix n n ℂ) (_hW : W.PosSemidef) (_hE : E.IsHermitian),
    R.readout () () 0 (Matrix.trace (W * E^2)).re
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (n := ULift.{u} Unit) 0 0 Matrix.PosSemidef.zero (by simp)
private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfCubicRadial.trace_weight_square_nonneg.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨
    @_root_.D5.S3.Quantum.Matrix.HsfCubicRadial.trace_weight_square_nonneg.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfCubicRadial.trace_weight_square_nonneg.{u}) (Realization pairSignature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfCubicRadial.WeightedSquare.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfCubicRadial.WeightedSquare.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.HsfCubicRadial
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
  options := #[]
end WeightedSquare

end

end Reg.D5.S3.Quantum.Matrix.HsfCubicRadial
