import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ArithSums.GiniStationaryTest.Result
import Reg.D5.S3.ArithSums.GiniStationaryTest.Witness

/-! Observation families for Gini comparison statements. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ArithSums.GiniStationaryTest.Defs
open _root_.D5.S3.ArithSums.GiniStationaryTest.Result

noncomputable section
namespace Reg.D5.S3.ArithSums.GiniStationaryTest.Result

abbrev signature := Witness.Nonmembership.signature
abbrev actual := Witness.Nonmembership.actual
abbrev rejected := Witness.Nonmembership.rejected
def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 3 ≤ n → stationaryTest n 1 0 2 (-1) ∧
    (((1,0),(2,-1)) : (ℝ × ℝ) × (ℝ × ℝ)) ∉ R.readout () () n
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 3 le_rfl).2 (Set.mem_univ _)
def evidence : Registration arena (type_of% (@counterexample_family)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨counterexample_family, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := Witness.Nonmembership.evidence.dependence

def registration_counterexample_family : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@counterexample_family)
    (type_of% (realize signature
      (fun _ _ n => Gamma n (Set.Ioi 0)) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.ArithSums.GiniStationaryTest.Result.counterexample_family.information_unit
  realizationName := `Reg.D5.S3.ArithSums.GiniStationaryTest.Result.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ n => Gamma n (Set.Ioi 0)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.GiniStationaryTest.Result
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.ArithSums.GiniStationaryTest.Result
