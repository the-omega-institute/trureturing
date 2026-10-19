import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.AlternatingGcdSumPillai
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Factorization.AlternatingGcdSumPillai
open LeanInformationAudit Finset

noncomputable section
namespace Reg.D5.S3.Factorization.AlternatingGcdSumPillai

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ d => Nat.totient d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_hn : n ≠ 0),
    pillai n = ∑ d ∈ n.divisors, R.readout () () d * (n / d)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by norm_num)
  norm_num [rejected, realize, pillai] at hh

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pillai_divisors, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), 1, 3, ?_⟩
    norm_num [actual, realize, Nat.totient_prime (by decide : Nat.Prime 3)]

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Factorization.AlternatingGcdSumPillai.pillai_divisors)
    (type_of% (realize signature (fun _ _ d => Nat.totient d) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Factorization.AlternatingGcdSumPillai.totient_information_unit
  realizationName := `Reg.D5.S3.Factorization.AlternatingGcdSumPillai.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => Nat.totient d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Factorization.AlternatingGcdSumPillai
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Factorization.AlternatingGcdSumPillai
