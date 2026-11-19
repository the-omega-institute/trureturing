import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Additive.PlasticTenPointEquality
import Reg.Support.SingleDependentReadout

/-! The full ten-point classification law, observed through its template count
on actual ten-point exponent sets. -/

namespace Reg.D5.S3.Arith.Additive.PlasticTenPointEquality

open _root_.D5.S3.Arith.Additive.PlasticTenPointEquality
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
  Law R := ∀ (E : Finset ℤ) (_hcard : E.card = 10),
    let classified := ∃ a : ℤ,
      E=(Finset.Icc (0:ℤ) 9).image (fun z => a+z) ∨
      E=(insert (0:ℤ) (Finset.Icc 2 10)).image (fun z => a+z) ∨
      E=(({0,1}:Finset ℤ) ∪ Finset.Icc 3 10).image (fun z => a+z) ∨
      E=(({0,3}:Finset ℤ) ∪ Finset.Icc 5 12).image (fun z => a+z)
    (R.readout () () E=14 ↔ classified) ∧
    ∀ r : ℝ, 1<r → r^3=r+1 →
      (((E.image (fun z => r^z))+(E.image (fun z => r^z))).card=41 ↔ classified)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : (Finset.Icc (0:ℤ) 9).card = 10 := by decide
  have hh := (h (Finset.Icc 0 9) he).1.mpr
    ⟨0, Or.inl (by simp)⟩
  change (15:ℕ)=14 at hh
  omega

private theorem actual_dependence : ObservationalDependence signature actual := by
  change ∀ _ : Unit, ∃ _ : Unit, ∃ A B : Finset ℤ, count A ≠ count B
  intro i
  let A : Finset ℤ := Finset.Icc 0 9
  let B : Finset ℤ := (Finset.range 10).image (fun i : ℕ => 10*(i:ℤ))
  have hA : A.card=10 := by decide +kernel
  have hB : B.card=10 := by decide +kernel
  refine ⟨(),A,B,?_⟩
  decide +kernel

def realization : Registration arena (type_of% (@whole_ten_point_equality)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨whole_ten_point_equality, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.Additive.PlasticTenPointEquality.whole_ten_point_equality)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Additive.PlasticTenPointEquality.whole_ten_point_equality.__information_unit
  realizationName := `Reg.D5.S3.Arith.Additive.PlasticTenPointEquality.realization
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
    owner := `D5.S3.Arith.Additive.PlasticTenPointEquality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms realization
#print axioms audit

end Reg.D5.S3.Arith.Additive.PlasticTenPointEquality
