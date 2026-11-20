import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Additive.PlasticExtremal
import D5.S3.Arith.SumProductGoldenMinimizerRefutation
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the complete original extremal theorem. The observed
quantity is the actual template count on every finite signed integer set, not
an entry of the finite certificate. Only one literal occurrence is varied;
all hypotheses and all four conclusion clauses remain in the reconstructed Law. -/

namespace Reg.D5.S3.Arith.Additive.PlasticExtremal

open _root_.D5.S3.Arith.Additive.PlasticExtremal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Pointwise

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Finset ℤ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ E => count E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 15) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r : ℝ) (_hr : 1 < r) (_hroot : r ^ 3 = r + 1)
    (n : ℕ) (_hn : 10 ≤ n),
    (∀ E : Finset ℤ, E.card=n → R.readout () () E ≤ 4*n-26 ∧
      n*(n+1)/2-4*n+26 ≤ ((E.image fun z => r^z)+(E.image fun z => r^z)).card) ∧
    (∀ a : ℤ, let E := Finset.Icc a (a+(n:ℤ)-1)
      E.card=n ∧ count E=4*n-26 ∧
      ((E.image fun z => r^z)+(E.image fun z => r^z)).card=n*(n+1)/2-4*n+26) ∧
    IsLeast {m : ℕ | ∃ A : Finset ℝ,
      (↑A : Set ℝ) ⊆ Set.range (fun z : ℤ => r^z) ∧ A.card=n ∧ (A+A).card=m}
      (n*(n+1)/2-4*n+26) ∧
    IsLeast {N : ℤ | ∀ E : Finset ℤ, N ≤ (E.card : ℤ) →
      (count E : ℤ) ≤ 4*(E.card : ℤ)-26} 10

private theorem rejected_law : ¬ arena.Law rejected := by
  obtain ⟨r, hr, _hr2, hroot⟩ :=
    _root_.D5.S3.Arith.SumProductGoldenMinimizerRefutation.plastic_root
  intro h
  have hcard : (Finset.Icc (0 : ℤ) 9).card = 10 := by decide
  have hh := ((h r hr hroot 10 (by decide)).1 (Finset.Icc 0 9) hcard).1
  change (15 : ℕ) ≤ 4 * 10 - 26 at hh
  omega

def family : Registration arena (type_of% (@whole_theorem_three_one)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨whole_theorem_three_one, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨(), ∅, ({0,2,3,4} : Finset ℤ), ?_⟩
    change count ∅ ≠ count ({0,2,3,4} : Finset ℤ)
    decide +kernel

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.Additive.PlasticExtremal.whole_theorem_three_one)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Additive.PlasticExtremal.whole_theorem_three_one.__information_unit
  realizationName := `Reg.D5.S3.Arith.Additive.PlasticExtremal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ E => count E) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Additive.PlasticExtremal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg",
        "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.Additive.PlasticExtremal
