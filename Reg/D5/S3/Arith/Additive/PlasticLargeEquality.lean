import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Additive.PlasticLargeEquality
import Reg.Support.SingleDependentReadout

/-! The complete large-cardinality classification law, observed through its
template count on actual integer exponent sets of cardinality at least eleven. -/

namespace Reg.D5.S3.Arith.Additive.PlasticLargeEquality

open _root_.D5.S3.Arith.Additive.PlasticLargeEquality
open _root_.D5.S3.Arith.Additive.PlasticExtremal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Pointwise

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Finset ℤ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ E => count E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 19) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (E : Finset ℤ) (_hn : 11≤E.card),
    let n := E.card
    let classified := ∃ a : ℤ,
      E=(Finset.Icc (0:ℤ) ((n:ℤ)-1)).image (fun z => a+z) ∨
      E=(insert (0:ℤ) (Finset.Icc 2 (n:ℤ))).image (fun z => a+z)
    (R.readout () () E=4*n-26 ↔ classified) ∧
    ∀ r : ℝ, 1<r → r^3=r+1 →
      (((E.image (fun z => r^z))+(E.image (fun z => r^z))).card=
        n*(n+1)/2-4*n+26 ↔ classified)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : 11 ≤ (Finset.Icc (0:ℤ) 10).card := by decide
  have hh := (h (Finset.Icc 0 10) he).1.mpr
    ⟨0, Or.inl (by norm_num)⟩
  change (19:ℕ)=4*(Finset.Icc (0:ℤ) 10).card-26 at hh
  norm_num at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  change ∀ _ : Unit, ∃ _ : Unit, ∃ A B : Finset ℤ, count A ≠ count B
  intro i
  let A : Finset ℤ := Finset.Icc 0 10
  let B : Finset ℤ := (Finset.range 11).image (fun i : ℕ => 10*(i:ℤ))
  have hA : A.card=11 := by decide +kernel
  have hB : B.card=11 := by decide +kernel
  refine ⟨(),A,B,?_⟩
  decide +kernel

def realization : Registration arena (type_of% (@whole_large_equality)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨whole_large_equality, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.Additive.PlasticLargeEquality.whole_large_equality)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Additive.PlasticLargeEquality.whole_large_equality.__information_unit
  realizationName := `Reg.D5.S3.Arith.Additive.PlasticLargeEquality.realization
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨realization⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ E => count E) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Additive.PlasticLargeEquality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms realization
#print axioms audit

end Reg.D5.S3.Arith.Additive.PlasticLargeEquality
