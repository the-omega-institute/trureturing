import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
import Reg.Support.DependentFamily

/- Candidate source-bound registration attempt.  The exact universal law and
   source bridge are retained below.  Contract.Registration is intentionally
   not asserted until an independent audit supplies whole-family variation,
   sensitivity, sourceSelection, and current producer binding evidence. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder

open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime tail)
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

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
  realize signature (fun _ _ m => correction m) (fun e => nomatch e)

/-- The full original telescope is retained, with the same-integer correction
    as the realized readout.  Both P and X endpoints remain in the law. -/
abbrev arena : Arena where
  signature := signature
  Law V := ∀ epsilon : ℝ, 0 < epsilon →
    ∃ T : ℝ, 1 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      T ≤ (largestPrime m : ℝ) →
      1 < Chebyshev.theta (largestPrime m : ℝ) ∧
      1 < Real.log (m : ℝ) ∧
      (let P : ℝ := largestPrime m
       let X := Real.log (m : ℝ)
       let C := V.readout () lambda m
       |Real.log P * (Real.sqrt P * Real.log P * C - 2 * Real.sqrt 2) +
          Real.sqrt 2 * (2 + Real.log 2)| < epsilon ∧
      |Real.log X * (Real.sqrt X * Real.log X * C - 2 * Real.sqrt 2) +
          Real.sqrt 2 * (2 + Real.log 2)| < epsilon)

private theorem actual_law : arena.Law actual := by
  exact @price_record_full_arithmetic_correction_second_order

private theorem source_bridge :
    (type_of% (@price_record_full_arithmetic_correction_second_order)) ↔ arena.Law actual := Iff.rfl

/- The dependent-family audit remains concrete and open: a later writer must
   provide a lawful rejected family, whole-family variation and sensitivity
   with the other coordinates fixed, observational dependence on both lambda
   and m, exact readout/sourceSelection coordinates for `correction`, and a
   current producer binding certificate.  This file does not fabricate any of
   those obligations or claim `declared_validated`. -/

#print axioms actual_law
#print axioms source_bridge

end Reg.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
