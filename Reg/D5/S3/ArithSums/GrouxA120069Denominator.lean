import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ArithSums.GrouxA120069Denominator
import Reg.Support.SingleDependentReadout

/-! A whole positive-index denominator readout with a nonconstant actual family. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ArithSums.GrouxA120069Denominator
open LeanInformationAudit
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.ArithSums.GrouxA120069Denominator
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n =>
    (∑ k ∈ Finset.Icc 1 n, (catalan k : ℚ) / (4 : ℚ)^(k-1)).den)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Only the original left denominator is varied; all positive indices remain. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 0 < n → R.readout () () n =
    ((catalan n : ℚ) / (4 : ℚ)^(n-1)).den

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 Nat.zero_lt_one
  norm_num [rejected, realize, catalan_one] at hbad

def evidence : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), (1 : ℕ), (2 : ℕ), ?_⟩
    change (∑ k ∈ Finset.Icc 1 1, (catalan k : ℚ) / (4 : ℚ)^(k-1)).den ≠
      (∑ k ∈ Finset.Icc 1 2, (catalan k : ℚ) / (4 : ℚ)^(k-1)).den
    rw [result 1 (by omega), result 2 (by omega)]
    norm_num [catalan_one, catalan_two]

def registration_result : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (Realization signature) Unit Unit := {
  unitName := `D5.S3.ArithSums.GrouxA120069Denominator.result.information_unit
  realizationName := `Reg.D5.S3.ArithSums.GrouxA120069Denominator.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n =>
    (∑ k ∈ Finset.Icc 1 n, (catalan k : ℚ) / (4 : ℚ)^(k-1)).den)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.GrouxA120069Denominator
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.ArithSums.GrouxA120069Denominator
