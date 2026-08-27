/- GID: D5/S3/Analytic/Connectivity/GoldenDisplacementSeriesValueConnectedness
   generality: I
   mirror-B: D5/B/S3/Analytic/Connectivity/GoldenDisplacementSeriesValueConnectedness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The attained golden displacement values are path-connected with no gaps above one. -/

/- Library-search audit trail (2026-08-27):
* Searches of `D5/**/*.lean` and `Blueprint/**/*.scribe.cs` for the proposed names,
  the full value-set comprehension, path-connectedness, connectedness, and no-gap
  statements found only the rejected unfrozen draft revised here. The repository
  supplies the exact convexity, continuity, greatest-lower-bound, and nonattainment
  inputs imported below.
* Searches of pinned `Mathlib/**/*.lean` found `Convex.isPathConnected`,
  `IsPathConnected.image'`, `IsPathConnected.isConnected`, `IsGLB.exists_between'`,
  and `IsPreconnected.ordConnected`. The greatest-lower-bound and nonattainment facts
  give an attained witness strictly between one and two, hence a point in the parameter
  domain. The first two lemmas give the path-connected image; the last two supply the
  order-connected interval inclusion used in the no-gap proof.
-/

import D5.S3.Analytic.Boundary.GoldenDisplacementSeriesContinuity
import D5.S3.Analytic.Displacement.GoldenDisplacementRegionConvexity
import D5.S3.Analytic.Extrema.GoldenDisplacementSeriesInfimum

open GoldenDisplacementEulerProduct
open GoldenDisplacementRegionConvexity
open D5.S3.Analytic.Boundary.GoldenDisplacementSeriesContinuity
open D5.S3.Analytic.Extrema.GoldenDisplacementSeriesInfimum

namespace D5.S3.Analytic.Connectivity.GoldenDisplacementSeriesValueConnectedness

/-- The values of convergent golden displacement series form a path-connected subset of `Real`. -/
theorem golden_displacement_series_values_isPathConnected :
    IsPathConnected
      {x : ℝ | ∃ s w : ℝ, Summable (dTerm s w) ∧ ∑' n : ℕ, dTerm s w n = x} := by
  obtain ⟨_, ⟨s, w, hsum, _⟩, _, _⟩ :=
    golden_displacement_series_isGLB.exists_between'
      one_not_mem_golden_displacement_series_values one_lt_two
  have himage :
      IsPathConnected
        ((fun p : ℝ × ℝ => ∑' n : ℕ, dTerm p.1 p.2 n) ''
          {p : ℝ × ℝ | Summable (dTerm p.1 p.2)}) :=
    (golden_displacement_convergence_region_convex.isPathConnected
        ⟨(s, w), hsum⟩).image' golden_displacement_series_continuousOn
  rw [show
    (fun p : ℝ × ℝ => ∑' n : ℕ, dTerm p.1 p.2 n) ''
        {p : ℝ × ℝ | Summable (dTerm p.1 p.2)} =
      {x : ℝ | ∃ s w : ℝ, Summable (dTerm s w) ∧ ∑' n : ℕ, dTerm s w n = x} by
    ext x
    constructor
    · rintro ⟨⟨s, w⟩, hsum, rfl⟩
      exact ⟨s, w, hsum, rfl⟩
    · rintro ⟨s, w, hsum, rfl⟩
      exact ⟨(s, w), hsum, rfl⟩] at himage
  exact himage

/-- Every value strictly between one and an attained value is itself attained. -/
theorem Ioo_one_subset_golden_displacement_series_values :
    ∀ x ∈ {y : ℝ | ∃ s w : ℝ, Summable (dTerm s w) ∧ ∑' n : ℕ, dTerm s w n = y},
      Set.Ioo 1 x ⊆
        {y : ℝ | ∃ s w : ℝ, Summable (dTerm s w) ∧ ∑' n : ℕ, dTerm s w n = y} := by
  intro x hx y hy
  obtain ⟨z, hz, _, hzy⟩ := golden_displacement_series_isGLB.exists_between'
    one_not_mem_golden_displacement_series_values hy.1
  exact
    golden_displacement_series_values_isPathConnected.isConnected.isPreconnected.ordConnected.out
      hz hx ⟨hzy.le, hy.2.le⟩

end D5.S3.Analytic.Connectivity.GoldenDisplacementSeriesValueConnectedness
