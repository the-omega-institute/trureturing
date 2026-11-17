import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Additive.PlasticDeletionBound
import D5.S3.Arith.SumProductGoldenMinimizerRefutation
import Reg.Support.SingleDependentReadout

/-! The complete deletion theorem observed through the cardinality of its real power set. -/

namespace Reg.D5.S3.Arith.Additive.PlasticDeletionBound

open _root_.D5.S3.Arith.Additive.PlasticDeletionBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Pointwise

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Finset ℝ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ A => A.card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r : ℝ) (_hr : 1 < r) (_hroot : r^3=r+1)
    (n h : ℕ) (_hn : 8 ≤ n) (_hh : 11*h+24 ≤ 3*n) (a : ℤ) (H : Finset ℤ)
    (_hH : H ⊆ Finset.Icc a (a+((n+h:ℕ):ℤ)-1)) (_hcardH : H.card=h),
    let I := Finset.Icc a (a+((n+h:ℕ):ℤ)-1)
    let E := I \ H
    let A := E.image (fun e => r^e)
    let G := (Finset.Icc (0:ℤ) ((n:ℤ)-1)).image (fun e => Real.goldenRatio^e)
    R.readout () () A=n ∧ (A*A).card ≤ 2*(n+h)-1 ∧ 2*(n+h)-1 ≤ 3*n-4 ∧
      (A+A).card ≤ n*(n+1)/2-4*n+26+11*h ∧
      n*(n+1)/2-4*n+26+11*h ≤ (G+G).card-1

private theorem rejected_law : ¬ arena.Law rejected := by
  obtain ⟨r, hr, _hr2, hroot⟩ :=
    _root_.D5.S3.Arith.SumProductGoldenMinimizerRefutation.plastic_root
  intro h
  have hh := (h r hr hroot 8 0 (by decide) (by decide) 0 ∅
    (by simp) (by simp)).1
  change (0 : ℕ) = 8 at hh
  omega

private theorem actual_dependence : ObservationalDependence signature actual := by
  classical
  change ∀ _ : Unit, ∃ _ : Unit, ∃ A B : Finset ℝ, A.card ≠ B.card
  intro i
  obtain ⟨r, hr, _hr2, hroot⟩ :=
    _root_.D5.S3.Arith.SumProductGoldenMinimizerRefutation.plastic_root
  let A := (Finset.Icc (0 : ℤ) 7).image (fun e => r^e)
  let B := (Finset.Icc (0 : ℤ) 8).image (fun e => r^e)
  refine ⟨(), A, B, ?_⟩
  change A.card ≠ B.card
  have hA : A.card = 8 := by
    have hh := (whole_theorem_four_one r hr hroot 8 0 (by decide) (by decide)
      0 ∅ (by simp) (by simp)).1
    simpa only [Finset.sdiff_empty, Nat.add_zero, Nat.cast_ofNat, zero_add, Int.reduceSub, A] using hh
  have hB : B.card = 9 := by
    have hh := (whole_theorem_four_one r hr hroot 9 0 (by decide) (by decide)
      0 ∅ (by simp) (by simp)).1
    simpa only [Finset.sdiff_empty, Nat.add_zero, Nat.cast_ofNat, zero_add, Int.reduceSub, B] using hh
  exact fun he => (by omega : (8 : ℕ) ≠ 9) (hA.symm.trans (he.trans hB))



def realization : Registration arena (type_of% (@whole_theorem_four_one)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨whole_theorem_four_one, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.Additive.PlasticDeletionBound.whole_theorem_four_one)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Additive.PlasticDeletionBound.whole_theorem_four_one.__information_unit
  realizationName := `Reg.D5.S3.Arith.Additive.PlasticDeletionBound.realization
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨realization⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => A.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Additive.PlasticDeletionBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms realization
#print axioms audit

end Reg.D5.S3.Arith.Additive.PlasticDeletionBound
