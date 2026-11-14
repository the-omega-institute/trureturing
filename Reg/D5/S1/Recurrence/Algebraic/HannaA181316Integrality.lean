import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.HannaA181316Integrality
import Reg.Support.SingleDependentReadout

/-! The coefficient readout preserves the full natural-degree and integer-witness family. -/

namespace Reg.D5.S1.Recurrence.Algebraic.HannaA181316Integrality
open _root_.D5.S1.Recurrence.Algebraic.HannaA181316Integrality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℤ × ℕ)
    (fun _ => PowerSeries ℚ) (fun _ => ℚ)

def actual : Realization signature :=
  realize signature (fun _ m f => coeff m.2 f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1 / 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ q : ℤ, 1 < q → ∀ m : ℕ, ∃ z : ℤ, R.readout () (q, m) (A q) = (z : ℚ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨z, hz⟩ := h 2 (by norm_num) 0
  change (1 / 2 : ℚ) = (z : ℚ) at hz
  have hd := congrArg Rat.den hz
  norm_num at hd

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(2, 0), 0, 1, ?_⟩
    change coeff 0 (0 : PowerSeries ℚ) ≠ coeff 0 (1 : PowerSeries ℚ)
    simp

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    result (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Algebraic.HannaA181316Integrality.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA181316Integrality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m f => coeff m.2 f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.HannaA181316Integrality
    definition := some {
      owner := `D5.S1.Recurrence.Algebraic.HannaA181316Integrality
      name := `D5.S1.Recurrence.Algebraic.HannaA181316Integrality.claim
      path := #[] }
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Recurrence.Algebraic.HannaA181316Integrality
