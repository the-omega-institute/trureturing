import D5.S3.Arith.Robin.PriceRecord.ActualCriticalChainNearbyGlobal
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/- Exact full-source laws and equivalence bridges only. Four-slot registration
remains unfinished under https://github.com/the-omega-institute/trureturing/issues/29429:
compiler occurrence/source binding, whole-family intervention and variation,
fixed-other-readout sensitivity and actual observational dependence are absent.
No Contract.Registration or declared_validated result is asserted. -/

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualCriticalChainNearbyGlobal

open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace actual_record_nearby_least_global_optimizer

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
  realize signature (fun _ t n => goldenResourceObjective t n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law W := ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
      (∀ n : ℕ, 0 < n → n < m →
        W.readout () mu n < W.readout () mu m) →
      T ≤ (largestPrime m : ℝ) →
      ∃ r : ℕ, ∃ t : ℝ, 1 < r ∧ r < m ∧ mu < t ∧
        Real.log (8 * (largestPrime m : ℝ)) ≤ Real.log ((m : ℝ) / r) ∧
        Real.log ((m : ℝ) / r) ≤
          C * Real.log (largestPrime m : ℝ) * Real.log (Real.log (largestPrime m : ℝ)) ∧
        (∀ n : ℕ, 0 < n → W.readout () t n ≤ W.readout () t r) ∧
        (∀ n : ℕ, 0 < n →
          W.readout () t n = W.readout () t r → r ≤ n)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualCriticalChainNearbyGlobal.actual_record_nearby_least_global_optimizer

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualCriticalChainNearbyGlobal.actual_record_nearby_least_global_optimizer)) ↔
      arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge

end actual_record_nearby_least_global_optimizer

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualCriticalChainNearbyGlobal
