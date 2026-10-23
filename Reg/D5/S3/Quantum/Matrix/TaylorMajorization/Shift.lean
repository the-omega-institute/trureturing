import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.TaylorMajorization.Shift
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
import Reg.D5.S3.Quantum.Matrix.LinGProperty.Normalization

/-! Source-bound readout registrations for Taylor majorization. -/

noncomputable section
open Matrix BigOperators Finset
open _root_.D5.S3.Quantum.Matrix.TaylorMajorization.Defs
open _root_.D5.S3.Quantum.Matrix.TaylorMajorization.Shift
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Quantum.Matrix.TaylorMajorization.Shift

namespace Coefficient
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin n) (Fin n) ℂ) (fun n => Matrix (Fin n) (Fin n) ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (k : ℕ),
    R.readout () n (taylorQ (A + s • 1) B k)
      (∑ j ∈ range (k + 1), ((k.choose j : ℂ) * s ^ (k-j)) • taylorQ A B j)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 0 0 0 0
def source_registration : Registration arena (type_of% @taylorQ_shift) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@taylorQ_shift, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := _root_.Reg.D5.S3.Quantum.Matrix.LinGProperty.Normalization.ZeroBlock.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@taylorQ_shift) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.TaylorMajorization.Shift.taylorQ_shift.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.TaylorMajorization.Shift.Coefficient.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.TaylorMajorization.Shift
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Coefficient

namespace Symmetrization
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (k : ℕ),
    R.readout () () (taylorR A B k).trace.re (taylorQ A B k).trace.re
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 0 0 0
def source_registration : Registration arena (type_of% @trace_taylorR) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@trace_taylorR, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := _root_.Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm.equality_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@trace_taylorR) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.TaylorMajorization.Shift.trace_taylorR.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.TaylorMajorization.Shift.Symmetrization.source_registration
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
    owner := `D5.S3.Quantum.Matrix.TaylorMajorization.Shift
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
  options := #[] }
end Symmetrization

namespace Defect
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (k : ℕ),
    R.readout () () (defect (A + (s : ℂ) • 1) B k)
      (∑ j ∈ range (k + 1), (k.choose j : ℝ) * s ^ (k-j) * defect A B j)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 0 0 0 0
def source_registration : Registration arena (type_of% @defect_shift) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@defect_shift, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := _root_.Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm.equality_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@defect_shift) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.TaylorMajorization.Shift.defect_shift.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.TaylorMajorization.Shift.Defect.source_registration
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
    owner := `D5.S3.Quantum.Matrix.TaylorMajorization.Shift
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
  options := #[] }
end Defect

end Reg.D5.S3.Quantum.Matrix.TaylorMajorization.Shift
