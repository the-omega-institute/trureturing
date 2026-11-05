import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.CompleteTailSecondOrder
import Reg.Support.DependentFamily

/- Candidate only: the exact complete-tail theorem and its source readout are
   prepared below, but no Contract.Registration is asserted. Independent
   review must establish whole-family variation/sensitivity, observational
   dependence, lawful sourceSelection and current binding evidence before any
   freeze or declared_validated status. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Robin.PriceRecord.CompleteTailSecondOrder

open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime tail)
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.PriceRecord.CompleteTailSecondOrder
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
  realize signature (fun _ _ m => tail m) (fun e => nomatch e)

/-- The exact original telescope is retained; only the Euler-tail readout is
reconstructed by the realization. -/
abbrev arena : Arena where
  signature := signature
  Law V := ∀ epsilon : ℝ, 0 < epsilon →
    ∃ T : ℝ, 1 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      T ≤ (largestPrime m : ℝ) →
      |Real.log (largestPrime m : ℝ) *
        (Real.sqrt (largestPrime m : ℝ) * Real.log (largestPrime m : ℝ) *
          V.readout () lambda m - Real.sqrt 2) +
        Real.sqrt 2 * (2 + Real.log 2 / 2)| < epsilon

private theorem actual_law : arena.Law actual := by
  exact @price_record_complete_tail_second_order

private theorem source_bridge :
    (type_of% (@price_record_complete_tail_second_order)) ↔ arena.Law actual := Iff.rfl

/- The following obligations intentionally remain with the later registration
writer: a lawful rejected family and whole-family variation/sensitivity,
actual observational dependence on the source state/parameter, exact enrolled
readout/sourceSelection coordinates, and current producer binding evidence.
This candidate therefore does not define Contract.Registration or claim
 declared_validated. -/

#print axioms actual_law
#print axioms source_bridge

end Reg.D5.S3.Arith.Robin.PriceRecord.CompleteTailSecondOrder
