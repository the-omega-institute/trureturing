/- GID: D5/S3/Topology/Measures/NormPreservingLiftExistence
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/NormPreservingLiftExistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact metric quotient maps admit total-variation-preserving signed lifts -/

import D5.S3.Topology.Selection.Measurable
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# Total-variation-preserving signed lifts

A Borel right inverse supplies a lift of every finite signed measure.
Total variation contracts under each of the two measurable pushforwards;
the right-inverse identity forces equality of the total masses.
No normed-space structure on `SignedMeasure` is required.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set MeasureTheory

namespace D5.S3.Topology.Measures.NormPreservingLiftExistence

/-- Every finite signed measure on a Hausdorff Borel quotient of a compact
metric space has a signed lift with exactly the same total variation mass. -/
theorem exists_norm_preserving_lift {K : Type*} [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] {L : Type*} [TopologicalSpace L] [T2Space L]
    [MeasurableSpace L] [BorelSpace L] (p : K → L) (hp : Continuous p)
    (hsurj : Function.Surjective p) (nu : SignedMeasure L) :
    ∃ s : SignedMeasure K, s.map p = nu ∧
      s.totalVariation univ = nu.totalVariation univ := by
  obtain ⟨q, hq, hright⟩ :=
    Selection.Measurable.exists_measurable_right_inverse p hp hsurj
  have hmap : (nu.map q).map p = nu := by
    apply VectorMeasure.ext
    intro A hA
    rw [VectorMeasure.map_apply _ hp.measurable hA,
      VectorMeasure.map_apply _ hq (hp.measurable hA)]
    congr 1
    ext y
    simp only [mem_preimage, hright y]
  refine ⟨nu.map q, hmap, le_antisymm ?_ ?_⟩
  · have h := VectorMeasure.variation_map_le (μ := nu) (φ := q) univ
    simpa only [← SignedMeasure.totalVariation_eq_variation,
      Measure.map_apply hq MeasurableSet.univ, preimage_univ] using h
  · have h := VectorMeasure.variation_map_le (μ := nu.map q) (φ := p) univ
    simpa only [hmap, ← SignedMeasure.totalVariation_eq_variation,
      Measure.map_apply hp.measurable MeasurableSet.univ, preimage_univ] using h

end D5.S3.Topology.Measures.NormPreservingLiftExistence
