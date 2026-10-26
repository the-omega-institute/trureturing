import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.TaylorMajorization.Defs
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm

/-! Source-bound readout registrations for Taylor majorization. -/

noncomputable section
open Matrix BigOperators Finset
open _root_.D5.S3.Quantum.Matrix.TaylorMajorization.Defs

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Quantum.Matrix.TaylorMajorization.Defs

namespace Trace
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℂ}
      {hX : X.IsHermitian} {hY : Y.IsHermitian}, weakMaj hX hY →
      R.readout () () X.trace.re Y.trace.re
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 0 0 isHermitian_zero isHermitian_zero (by
    intro r hr
    simp)
def source_registration : Registration arena (type_of% @weakMaj_trace) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weakMaj_trace, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := _root_.Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm.order_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@weakMaj_trace) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.TaylorMajorization.Defs.weakMaj_trace.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.TaylorMajorization.Defs.Trace.source_registration
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
    owner := `D5.S3.Quantum.Matrix.TaylorMajorization.Defs
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
  options := #[] }
end Trace

end Reg.D5.S3.Quantum.Matrix.TaylorMajorization.Defs
