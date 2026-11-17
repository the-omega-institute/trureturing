import D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/- Full-telescope actual laws and definitional source bridges.
Four-slot registration is unfinished: lawful enrolled-template application,
compiler occurrence/sourceSelection binding, whole-family intervention,
fixed-coordinate sensitivity and observational dependence remain unproved. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack
open Real Filter Finset
open scoped Topology BigOperators
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace bhp_actual_five_mode_small_slack
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
  realize signature (fun _ p x => goldenResourceObjective p x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := BHPMaximumGap → BHPShortIntervalCount →
      ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
        ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
          T ≤ (largestPrime m : ℝ) →
          let lambda := beta 1 (largestPrime m : ℝ)
          let Dtop := lambda * Real.log 2 -
            goldenLayerMarginal 2 (m.factorization 2) * Real.log 2
          ∃ n : ℕ, 0 < n ∧ n < m ∧
            let eta := Real.log (m : ℝ) - Real.log (n : ℝ)
            0 < eta ∧
            eta ≤ C * Real.log (Real.log (m : ℝ)) ^ (-(4 : ℝ)) ∧
            |((V.readout ()) lambda n - (V.readout ()) lambda m) - Dtop| ≤
              C * lambda * Real.log (Real.log (m : ℝ)) ^ 2 *
                (largestPrime m : ℝ) ^ (-(19 / 640 : ℝ)) ∧
            Dtop ≤ (lambda - mu) * eta +
              C * lambda * Real.log (Real.log (m : ℝ)) ^ 2 *
                (largestPrime m : ℝ) ^ (-(19 / 640 : ℝ))

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.bhp_actual_five_mode_small_slack

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.bhp_actual_five_mode_small_slack)) ↔ arena.Law actual := Iff.rfl

end bhp_actual_five_mode_small_slack

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack
