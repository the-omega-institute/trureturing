import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Additive.PlasticGappedFamily
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Arith.Additive.PlasticGappedFamily

open _root_.D5.S3.Arith.Additive.PlasticGappedFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Pointwise

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => Finset ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ n => family n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ n : ℕ, 10 ≤ n →
      (R.readout () () n).card = n ∧
      (0 : ℤ) ∈ family n ∧ (1 : ℤ) ∉ family n ∧ (2 : ℤ) ∈ family n ∧
      ((family n).filter fun t => t+2 ∈ family n ∧ t+3 ∈ family n ∧ t+4 ∈ family n).card +
      ((family n).filter fun t => t+3 ∈ family n ∧ t+5 ∈ family n ∧ t+6 ∈ family n).card +
      ((family n).filter fun t => t+5 ∈ family n ∧ t+7 ∈ family n).card +
      ((family n).filter fun t => t+5 ∈ family n ∧ t+8 ∈ family n ∧ t+9 ∈ family n).card = 4*n-26 ∧
      (∀ r : ℝ, 1 < r → r^3 = r+1 →
        ((family n).image fun e => r^e).card = n ∧
        (((family n).image fun e => r^e)+((family n).image fun e => r^e)).card =
          n*(n+1)/2-4*n+26)) ∧
    (∀ r : ℝ, 1 < r → r^3 = r+1 →
      let A := (family 9).image fun e => r^e
      let P := (Finset.Icc (0 : ℤ) 8).image fun e => r^e
      A.card = 9 ∧ P.card = 9 ∧ (A+A).card = 34 ∧ (P+P).card = 35 ∧
        (A+A).card < (P+P).card)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h.1 10 (by decide)).1
  change (∅ : Finset ℤ).card = 10 at hh
  norm_num at hh

def realization : Registration arena (type_of% (@whole_proposition_five_one)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨whole_proposition_five_one, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨(), 10, 11, ?_⟩
    change family 10 ≠ family 11
    decide +kernel

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.Additive.PlasticGappedFamily.whole_proposition_five_one)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Additive.PlasticGappedFamily.whole_proposition_five_one.__information_unit
  realizationName := `Reg.D5.S3.Arith.Additive.PlasticGappedFamily.realization
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨realization⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => family n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Additive.PlasticGappedFamily
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms realization
#print axioms audit

end Reg.D5.S3.Arith.Additive.PlasticGappedFamily
