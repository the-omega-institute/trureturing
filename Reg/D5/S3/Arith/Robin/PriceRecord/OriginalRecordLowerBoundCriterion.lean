import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.OriginalRecordLowerBoundCriterion
import Reg.Support.SingleDependentReadout

/-! The full original-record equivalence, with a variable original-margin readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.PriceRecord.OriginalRecordLowerBoundCriterion
open _root_.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (D)
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger (goldenResourceObjective)
open _root_.D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Robin.PriceRecord.OriginalRecordLowerBoundCriterion

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ m => robinLogMargin m) (fun e => nomatch e)

def zeroFamily : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∃ M T : ℝ, 2 ≤ T ∧ ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      T ≤ (largestPrime m : ℝ) →
      -M ≤ D (largestPrime m : ℝ) * R.readout () lambda m) ↔ RiemannHypothesis

private theorem actual_law : arena.Law actual := original_record_lower_bound_iff_rh

private theorem source_reconstruction :
    (type_of% @original_record_lower_bound_iff_rh) ↔ arena.Law actual := Iff.rfl

private theorem zero_bound :
    ∃ M T : ℝ, 2 ≤ T ∧ ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      T ≤ (largestPrime m : ℝ) →
      -M ≤ D (largestPrime m : ℝ) * zeroFamily.readout () lambda m := by
  refine ⟨0, 2, le_rfl, ?_⟩
  intro m hm lambda hlambda hrecord hlarge
  simp [zeroFamily, realize]

/-- A zero-margin candidate alone cannot refute the equivalence without not RH. -/
private theorem zero_law_iff_rh : arena.Law zeroFamily ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact h.mp zero_bound
  · intro hRH
    exact ⟨fun _ => hRH, fun _ => zero_bound⟩

/- This exact source law and bridge compile. A whole-family rejected law,
sensitivity, actual observational dependence, lawful source selection and
current four-slot binding are not supplied. No Contract.Registration is
asserted, and the zero-family calculation is not a variation certificate. -/

end Reg.D5.S3.Arith.Robin.PriceRecord.OriginalRecordLowerBoundCriterion
end
