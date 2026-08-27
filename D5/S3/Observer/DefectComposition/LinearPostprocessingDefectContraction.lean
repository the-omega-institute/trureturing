/- GID: D5/S3/Observer/DefectComposition/LinearPostprocessingDefectContraction
   generality: G
   mirror-B: D5/B/S3/Observer/DefectComposition/LinearPostprocessingDefectContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Linear postprocessing contracts distance to the realizable image by its operator norm. -/

import Mathlib

/- Library-search audit trail (2026-08-28):
   * Repository searches found no theorem combining point-to-set distance, a continuous linear
     map, and the image of a realizable set. The measurable postprocessing theorem concerns total
     variation and is not an exact hit.
   * The pinned Mathlib search found `Metric.infDist_le_dist_of_mem`,
     `IsClosed.exists_infDist_eq_dist`, and `ContinuousLinearMap.dist_le_opNorm`, which are applied
     below. `Metric.infDist_image` is restricted to isometries and is not an exact hit.
-/

namespace D5.S3.Observer.DefectComposition.LinearPostprocessingDefectContraction

/- A linear postprocessor cannot amplify distance to the image of a closed realizable set by
more than its operator norm; a normalized postprocessor is therefore contractive. -/
theorem linear_postprocessing_defect_contraction
    {Y Z : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (B : Y →L[ℝ] Z) (I : Set Y) (y : Y)
    (hIclosed : IsClosed I) (hIne : I.Nonempty) :
    Metric.infDist (B y) (B '' I) ≤ ‖B‖ * Metric.infDist y I ∧
      (‖B‖ ≤ 1 → Metric.infDist (B y) (B '' I) ≤ Metric.infDist y I) := by
  obtain ⟨x, hxI, hnearest⟩ := hIclosed.exists_infDist_eq_dist hIne y
  have hxImage : B x ∈ B '' I := ⟨x, hxI, rfl⟩
  have hgeneral : Metric.infDist (B y) (B '' I) ≤ ‖B‖ * Metric.infDist y I := by
    calc
      Metric.infDist (B y) (B '' I) ≤ dist (B y) (B x) :=
        Metric.infDist_le_dist_of_mem hxImage
      _ ≤ ‖B‖ * dist y x := B.dist_le_opNorm y x
      _ = ‖B‖ * Metric.infDist y I := by rw [hnearest]
  refine ⟨hgeneral, fun hB => hgeneral.trans ?_⟩
  exact mul_le_of_le_one_left Metric.infDist_nonneg hB

/- The closed singleton is a nontrivial admissible realizable set. -/
example :
    Metric.infDist ((ContinuousLinearMap.id ℝ ℝ) 3)
          ((ContinuousLinearMap.id ℝ ℝ) '' ({1} : Set ℝ)) ≤
        ‖ContinuousLinearMap.id ℝ ℝ‖ * Metric.infDist 3 ({1} : Set ℝ) ∧
      (‖ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 →
        Metric.infDist ((ContinuousLinearMap.id ℝ ℝ) 3)
            ((ContinuousLinearMap.id ℝ ℝ) '' ({1} : Set ℝ)) ≤
          Metric.infDist 3 ({1} : Set ℝ)) := by
  exact linear_postprocessing_defect_contraction
    (B := ContinuousLinearMap.id ℝ ℝ) (I := ({1} : Set ℝ)) (y := 3)
    isClosed_singleton (Set.singleton_nonempty 1)

#print axioms linear_postprocessing_defect_contraction

end D5.S3.Observer.DefectComposition.LinearPostprocessingDefectContraction
