import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.TaylorMajorization.Pauli
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
import Reg.D5.S3.Quantum.Matrix.LinGProperty.Normalization

/-! Source-bound readout registrations for Taylor majorization. -/

noncomputable section
open Matrix BigOperators Finset
open _root_.D5.S3.Quantum.Matrix.TaylorMajorization.Defs
open _root_.D5.S3.Quantum.Matrix.TaylorMajorization.Pauli
open _root_.D5.S3.Quantum.FiniteDimensional
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Quantum.Matrix.TaylorMajorization.Pauli

namespace Even
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), 1 ≤ m →
    R.readout () () (defect qubitZ qubitX (2*m)) ((4 : ℝ)^m - 2^(m+1))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega)
def source_registration : Registration arena (type_of% @defect_even) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@defect_even, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := _root_.Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm.equality_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@defect_even) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.TaylorMajorization.Pauli.defect_even.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.TaylorMajorization.Pauli.Even.source_registration
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
    owner := `D5.S3.Quantum.Matrix.TaylorMajorization.Pauli
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Even

namespace Odd
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ),
    R.readout () () (defect qubitZ qubitX (2*m+1)) 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0
def source_registration : Registration arena (type_of% @defect_odd) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@defect_odd, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := _root_.Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm.equality_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@defect_odd) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.TaylorMajorization.Pauli.defect_odd.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.TaylorMajorization.Pauli.Odd.source_registration
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
    owner := `D5.S3.Quantum.Matrix.TaylorMajorization.Pauli
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Odd

namespace Negative
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ), Odd k → 5 ≤ k → ∀ (t : ℝ), 0 < t →
    R.readout () () (defect (qubitZ - (t : ℂ) • 1) qubitX k) 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 5 (by decide) (by omega) 1 (by norm_num)
def source_registration : Registration arena (type_of% @defect_shift_negative) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@defect_shift_negative, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := _root_.Reg.D5.S3.Quantum.Matrix.LinGProperty.Normalization.PositiveTrace.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@defect_shift_negative) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.TaylorMajorization.Pauli.defect_shift_negative.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.TaylorMajorization.Pauli.Negative.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.TaylorMajorization.Pauli
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
end Negative

end Reg.D5.S3.Quantum.Matrix.TaylorMajorization.Pauli
