import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.LinGProperty.ScalarPerturbation
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for the matrix comparison prerequisites. -/

noncomputable section
set_option autoImplicit false
open Matrix
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Matrix.LinGProperty
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Quantum.Matrix.LinGProperty.ScalarPerturbation
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev Block (n : ℕ) := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ
namespace SingularValues
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (A : Mat n) (z : ℂ) (j : Fin (Fintype.card (Fin n))),
    R.readout () () (singularValuesSorted (A + z • 1) j) (singularValuesSorted A j + ‖z‖)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (n := 1) 0 0 ⟨0, by simp⟩
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% (@singularValuesSorted_add_scalar)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@singularValuesSorted_add_scalar, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@singularValuesSorted_add_scalar) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.singularValuesSorted_add_scalar.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.ScalarPerturbation.SingularValues.family
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
    owner := `D5.S3.Quantum.Matrix.LinGProperty.ScalarPerturbation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end SingularValues

namespace Eigenvalues
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (A : Mat n) (hA : A.IsHermitian) (r : ℝ)
    (hB : (A + (r : ℂ) • 1).IsHermitian) (j : Fin (Fintype.card (Fin n))),
    R.readout () () (hB.eigenvalues₀ j) (hA.eigenvalues₀ j + r)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (n := 1) 0 Matrix.isHermitian_zero 0 (by simp) ⟨0, by simp⟩
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% (@eigenvalues_zero_add_scalar)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eigenvalues_zero_add_scalar, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eigenvalues_zero_add_scalar) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.eigenvalues_zero_add_scalar.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.ScalarPerturbation.Eigenvalues.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.LinGProperty.ScalarPerturbation
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
end Eigenvalues

end Reg.D5.S3.Quantum.Matrix.LinGProperty.ScalarPerturbation
