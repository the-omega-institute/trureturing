import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.LinGProperty.PhaseRotation
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for phase normalization of positive block matrices. -/

noncomputable section
set_option autoImplicit false
open Matrix
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Matrix.LinGProperty
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Quantum.Matrix.LinGProperty.PhaseRotation
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev Block (n : ℕ) := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ

namespace SingularValues
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (X : Mat n) (z : ℂ), ‖z‖ = 1 →
    ∀ j : Fin (Fintype.card (Fin n)),
    R.readout () () (singularValuesSorted (z • X) j) (singularValuesSorted X j)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (n := 1) 0 1 (by norm_num) ⟨0, by simp⟩
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% (@singularValuesSorted_phase)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@singularValuesSorted_phase, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@singularValuesSorted_phase) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.singularValuesSorted_phase.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.PhaseRotation.SingularValues.family
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
    owner := `D5.S3.Quantum.Matrix.LinGProperty.PhaseRotation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end SingularValues

namespace TracePhase
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun n => Mat n) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ X => ‖X.trace‖) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (X : Mat n), ∃ z : ℂ,
    ‖z‖ = 1 ∧ (z • X).trace = (R.readout () n X : ℂ)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  obtain ⟨z, hz, ht⟩ := h (n := 1) 0
  have ht' := congrArg Complex.re ht
  norm_num [rejected, realize] at ht'
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% (@exists_trace_phase)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_trace_phase, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_trace_phase) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.exists_trace_phase.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.PhaseRotation.TracePhase.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => ‖X.trace‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.LinGProperty.PhaseRotation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end TracePhase

end Reg.D5.S3.Quantum.Matrix.LinGProperty.PhaseRotation
