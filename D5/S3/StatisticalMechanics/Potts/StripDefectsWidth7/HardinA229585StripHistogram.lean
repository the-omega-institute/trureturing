/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripHistogram
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripHistogram
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripHistogram.sum_filtered
   digest: Exact transfer histograms with horizontally inadmissible rows removed. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229585Strip.result)
Input: proof_shape=bind-only; consumers=histogram, sum_filtered
eligibleRows: proof_shape=bind-only; consumers=histogram, sum_filtered
histogram: proof_shape=bind-only; consumers=sum_filtered, width-seven transition_counts
sum_filtered: proof_shape=bind-only; consumers=width-seven transition_counts
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

/-! Finite-sum normalization before exact histogram verification. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripHistogram
open HardinA229585StripData
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)

abbrev Input := Boundary × Fin 2 × Fin 72

private def eligibleRows : Finset Row :=
  Finset.univ.filter fun r => bondDefects horizontal r r ≤ 1

def histogram (x : Input) : ℤ :=
  ∑ r ∈ eligibleRows, if cross x.1 r + bondDefects horizontal r r ≤ x.2.1.val ∧
      cl (boundary r) (x.2.1.val - (cross x.1 r + bondDefects horizontal r r)) = x.2.2
    then (1 : ℤ) else 0

theorem sum_filtered (x : Input) :
    (∑ r : Row, if cross x.1 r + bondDefects horizontal r r ≤ x.2.1.val ∧
      cl (boundary r) (x.2.1.val - (cross x.1 r + bondDefects horizontal r r)) = x.2.2
      then (1 : ℤ) else 0) = histogram x := by
  unfold histogram eligibleRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : bondDefects horizontal r r ≤ 1
  · simp only [h, ite_true]
  · have hn : ¬ cross x.1 r + bondDefects horizontal r r ≤ x.2.1.val := by
      have hd := x.2.1.isLt
      omega
    simp only [h, ite_false, hn, false_and]

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripHistogram
