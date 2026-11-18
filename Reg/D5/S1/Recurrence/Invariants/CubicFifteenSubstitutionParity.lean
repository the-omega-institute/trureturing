import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

open PowerSeries
open _root_.D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => PowerSeries (ZMod 2)) (fun _ => PowerSeries (ZMod 2))

def actual : Realization signature :=
  realize signature (fun _ _ u => u + u ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {u v : PowerSeries (ZMod 2)}, constantCoeff u = 0 →
    constantCoeff v = 0 → r.readout () () u = r.readout () () v → u = v

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (u := 0) (v := X) (by simp) (by simp) rfl
  have hc := congrArg (coeff 1) he
  simpa using hc

def family : Registration arena (type_of% @quadratic_unique) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quadratic_unique, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, X, ?_⟩
    intro he
    have hc := congrArg (coeff 1) he
    change coeff 1 ((0 : PowerSeries (ZMod 2)) + 0 ^ 2) =
      coeff 1 ((X : PowerSeries (ZMod 2)) + X ^ 2) at hc
    have hx : coeff 1 ((X : PowerSeries (ZMod 2)) ^ 2) = 0 :=
      (coeff_X_pow 1 2).trans (if_neg (by decide))
    simp only [map_add, map_zero, zero_pow (by decide : 2 ≠ 0),
      coeff_one_X, hx, add_zero, zero_add] at hc
    exact zero_ne_one hc

def quadratic_unique_audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@quadratic_unique) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.quadraticUniqueUnit
  realizationName := `Reg.D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => u + u ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "body", "domain", "fn", "arg"],
        stateBinder := 0, functionOperand := false, stateOperand := none,
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "domain", "arg"],
        stateBinder := 1, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms quadratic_unique_audit

end
end Reg.D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
