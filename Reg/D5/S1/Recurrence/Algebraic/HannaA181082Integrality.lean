import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.HannaA181082Integrality
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S1.Recurrence.Algebraic.HannaA181082Integrality

open _root_.D5.S1.Recurrence.Algebraic.HannaA181082Integrality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℚ)

def actual : Realization signature :=
  realize signature (fun _ _ m => coeff m A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1 / 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, ∃ z : ℤ, R.readout () () m = (z : ℚ)

private theorem rejected_bad : ¬ arena.Law rejected := by
  intro h
  obtain ⟨z, hz⟩ := h 0
  change (1 / 2 : ℚ) = (z : ℚ) at hz
  have hd := congrArg Rat.den hz
  norm_num at hd

private theorem actual_dependent : ObservationalDependence signature actual := by
  have hL0 : constantCoeff logarithm = 0 := by
    norm_num [logarithm, constantCoeff_mk, Finset.sum_range_succ]
  have hA0 : constantCoeff A = 1 := by
    change MvPowerSeries.constantCoeff (PowerSeries.subst logarithm (PowerSeries.exp ℚ)) = 1
    rw [constantCoeff_subst_of_constantCoeff_zero hL0]
    simp
  have hdL0 : constantCoeff (derivative logarithm) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
    norm_num [logarithm, coeff_mk, Finset.sum_range_succ]
  have hdL1 : coeff 1 (derivative logarithm) = 3 := by
    rw [coeff_derivative]
    norm_num [logarithm, coeff_mk, Finset.sum_range_succ, Nat.choose]
  have hder := _root_.D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality.expSeries_derivative hL0
  change derivative A = A * derivative logarithm at hder
  have hA1 : coeff 1 A = 1 := by
    have h := congrArg (coeff 0) hder
    simpa [coeff_derivative, coeff_zero_eq_constantCoeff, hA0, hdL0] using h
  have hA2 : coeff 2 A = 2 := by
    have h := congrArg (coeff 1) hder
    rw [coeff_derivative, coeff_one_mul, hA1, hdL0, hdL1, hA0] at h
    norm_num at h
    linarith
  intro i
  refine ⟨(), 0, 2, ?_⟩
  change coeff 0 A ≠ coeff 2 A
  rw [coeff_zero_eq_constantCoeff, hA0, hA2]
  norm_num

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_bad⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_bad
  dependence := actual_dependent

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    result (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Algebraic.HannaA181082Integrality.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA181082Integrality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => coeff m A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.HannaA181082Integrality
    definition := some {
      owner := `D5.S1.Recurrence.Algebraic.HannaA181082Integrality
      name := `D5.S1.Recurrence.Algebraic.HannaA181082Integrality.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Recurrence.Algebraic.HannaA181082Integrality
