import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.RHSharpOriginalRecordMargin
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Arith.Robin.PriceRecord.RHSharpOriginalRecordMargin
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open _root_.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (D B)
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)

namespace Reg.D5.S3.Arith.Robin.PriceRecord.RHSharpOriginalRecordMargin

abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => robinLogMargin x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ hRH : RiemannHypothesis,
    (∀ epsilon : ℝ, 0 < epsilon → ∃ T : ℝ, 2 ≤ T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      T ≤ (largestPrime m : ℝ) →
      K - epsilon < D (largestPrime m : ℝ) * V.readout () lambda m) ∧
    (∀ epsilon : ℝ, 0 < epsilon → ∀ Y : ℝ,
      ∃ m : ℕ, ∃ lambda : ℝ, 2 ≤ m ∧ 0 < lambda ∧
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) ∧
      Y < (largestPrime m : ℝ) ∧ 1 < Chebyshev.theta (largestPrime m : ℝ) ∧
      1 < Real.log (m : ℝ) ∧
      |D (largestPrime m : ℝ) * V.readout () lambda m - K| < epsilon)

private theorem actual_law : arena.Law actual := by
  exact @original_record_sharp_lower_endpoint

private theorem source_bridge :
    (type_of% (@original_record_sharp_lower_endpoint)) ↔ arena.Law actual := Iff.rfl

/- Whole-family registration is unfinished. These are the original source law,
   its actual realization, and its exact equivalence bridge only; no
   Contract.Registration is asserted. A lawful enrolled-template readout,
   whole-family variation, sensitivity, observational dependence, sourceSelection,
   and current binding evidence remain necessary. Refuting the whole conditional
   law for a rejected family entails RH: without RH this implication holds for
   every family. The source law has no added anchor equality. -/

end Reg.D5.S3.Arith.Robin.PriceRecord.RHSharpOriginalRecordMargin
