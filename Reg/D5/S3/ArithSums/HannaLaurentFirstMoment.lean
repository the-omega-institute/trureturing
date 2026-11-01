import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ArithSums.HannaLaurentFirstMoment
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ArithSums.HannaLaurentRowSums
open LeanInformationAudit
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.ArithSums.HannaLaurentFirstMoment
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ n k => rowEntry n k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Vary the integer coefficient observation while retaining both original conjuncts. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (hn : 0 < n),
    (∑ k ∈ Finset.range (rowBound n + 1), (k : ℤ) * R.readout () n k = 1) ∧
    (∑ k ∈ Finset.range (rowBound n + 1),
      (k : ℚ) * (series n hn).coeff (-(k : ℤ)) = 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 1 Nat.zero_lt_one).1
  simp [rejected, realize] at hbad

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.ArithSums.HannaLaurentFirstMoment.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ArithSums.HannaLaurentFirstMoment.result,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨1, 0, 1, ?_⟩
    norm_num [actual, realize, rowEntry, rowPolynomial, Polynomial.coeff_one]

def registration_result : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ArithSums.HannaLaurentFirstMoment.result)
    (type_of% (realize signature (fun _ n k => rowEntry n k) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.ArithSums.HannaLaurentFirstMoment.result.information_unit
  realizationName := `Reg.D5.S3.ArithSums.HannaLaurentFirstMoment.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => rowEntry n k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.HannaLaurentFirstMoment
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "arg", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.ArithSums.HannaLaurentFirstMoment
