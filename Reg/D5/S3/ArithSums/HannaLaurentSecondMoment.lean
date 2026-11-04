import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ArithSums.HannaLaurentSecondMoment
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ArithSums.HannaLaurentRowSums
open LeanInformationAudit
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.ArithSums.HannaLaurentSecondMoment
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℚ)

/-- The coefficient observation is total; the law uses only source-defined rows. -/
def actual : Realization signature :=
  realize signature (fun _ n k => if h : 0 < n then
    (series n h).coeff (-(k : ℤ)) else 0) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The original telescope, inclusive bound and signed right side are unchanged. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_hn : 2 ≤ n),
    (∑ k ∈ Finset.range (((n + 1) / 2)^2 + 1),
      (k : ℚ)^2 * R.readout () n k) = (-(2 * (n : ℤ) - 5) : ℤ)

private theorem bridge :
    (type_of% (@_root_.D5.S3.ArithSums.HannaLaurentSecondMoment.result)) ↔
      arena.Law actual := by
  constructor
  · intro h n hn
    simpa only [actual, realize, dif_pos (show 0 < n by omega)] using h n hn
  · intro h n hn
    simpa only [actual, realize, dif_pos (show 0 < n by omega)] using h n hn

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 2 (by omega)
  norm_num [rejected, realize] at hb

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.ArithSums.HannaLaurentSecondMoment.result)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp _root_.D5.S3.ArithSums.HannaLaurentSecondMoment.result,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨2, 0, 1, ?_⟩
    norm_num [actual, realize, series_coefficient, rowPolynomial,
      Finset.sum_range_succ, Polynomial.coeff_one]

def registration_result : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ArithSums.HannaLaurentSecondMoment.result)
    (type_of% (realize signature (fun _ n k => if h : 0 < n then
      (series n h).coeff (-(k : ℤ)) else 0) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.ArithSums.HannaLaurentSecondMoment.result.information_unit
  realizationName := `Reg.D5.S3.ArithSums.HannaLaurentSecondMoment.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => if h : 0 < n then
    (series n h).coeff (-(k : ℤ)) else 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.HannaLaurentSecondMoment
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.ArithSums.HannaLaurentSecondMoment
