import D5.S3.Arith.Robin.PriceRecord.ActualRecordSingleTwoTail
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/- The source law retains both analytic suppliers and the complete original
record telescope. A four-slot registration still needs lawful template/source
binding, whole-family variation and fixed-coordinate sensitivity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualRecordSingleTwoTail

open Real Filter Finset
open scoped Topology BigOperators
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace bhp_actual_record_single_two_tail

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => goldenLayerMarginal 2 k) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := BHPMaximumGap → BHPShortIntervalCount →
    ∃ T0 : ℝ, 0 < T0 ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
        T0 ≤ (largestPrime m : ℝ) →
        let c := 1 / (Real.log (m : ℝ) * Real.log (Real.log (m : ℝ)))
        let a := optimalLayerCount c 2
        let v := m.factorization 2
        v ≤ a + 1 ∧
          ∀ k : ℕ, 1 ≤ k → k ≤ v → V.readout () () k < c →
            v = a + 1 ∧ k = v ∧
            Icc (a + 1) v = {v} ∧
            (((v - a : ℕ) : ℝ) * Real.log 2 = Real.log 2) ∧
            (∑ j ∈ Icc (a + 1) v, (c - V.readout () () j) * Real.log 2) =
              (c - V.readout () () v) * Real.log 2

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordSingleTwoTail.bhp_actual_record_single_two_tail

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordSingleTwoTail.bhp_actual_record_single_two_tail)) ↔
      arena.Law actual := Iff.rfl

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change goldenLayerMarginal 2 1 ≠ goldenLayerMarginal 2 2
  exact ne_of_gt (golden_layer_strict_decrease Nat.prime_two (by norm_num) (by norm_num))

private theorem variation_requires_analytic_suppliers :
    Variation arena actual → BHPMaximumGap ∧ BHPShortIntervalCount := by
  rintro ⟨_, bad, hbad⟩
  constructor
  · by_contra hgap
    apply hbad
    intro hgap'
    exact (hgap hgap').elim
  · by_contra hcount
    apply hbad
    intro _ hcount'
    exact (hcount hcount').elim

end bhp_actual_record_single_two_tail

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualRecordSingleTwoTail
