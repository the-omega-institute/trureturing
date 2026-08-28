/- GID: D5/S3/Analytic/Boundary/GoldenDisplacementConvergenceBoundary
   generality: I
   mirror-B: D5/B/S3/Analytic/Boundary/GoldenDisplacementConvergenceBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identifies the topological boundary of golden displacement convergence. -/

/- Library-search audit trail (2026-08-26):
   * The repository theorem `dTerm_summable_iff_critical_boundary` identifies the
     convergence region with the strict epigraph used here.
   * Pinned Mathlib's `frontier_lt_subset_eq` proves only the frontier-to-equality
     inclusion for continuous functions. Its epigraph API supplies no applicable
     frontier equality, so the reverse inclusion below uses a vertical perturbation.
   * Repository Lean and Blueprint searches found no existing statement of this
     topological boundary.
-/

import D5.S3.Analytic.Displacement.GoldenDisplacementBindingConstraint

set_option autoImplicit false
set_option relaxedAutoImplicit false

open GoldenDisplacementEulerProduct
open GoldenDisplacementBindingConstraint

namespace D5.S3.Analytic.Boundary.GoldenDisplacementConvergenceBoundary

/-- The topological boundary of the golden displacement convergence region is
the graph of its critical-boundary function. -/
theorem golden_displacement_convergence_boundary :
    frontier {p : ℝ × ℝ | Summable (dTerm p.1 p.2)} =
      {p : ℝ × ℝ | goldenDisplacementCriticalBoundary p.1 = p.2} := by
  have hregion :
      {p : ℝ × ℝ | Summable (dTerm p.1 p.2)} =
        {p : ℝ × ℝ | goldenDisplacementCriticalBoundary p.1 < p.2} := by
    ext p
    exact dTerm_summable_iff_critical_boundary p.1 p.2
  rw [hregion]
  apply Set.Subset.antisymm
  · have hcontinuous : Continuous goldenDisplacementCriticalBoundary := by
      unfold goldenDisplacementCriticalBoundary
      fun_prop
    exact frontier_lt_subset_eq (hcontinuous.comp continuous_fst) continuous_snd
  · rintro ⟨s, w⟩ hp
    change goldenDisplacementCriticalBoundary s = w at hp
    rw [frontier_eq_closure_inter_closure]
    constructor
    · rw [Metric.mem_closure_iff]
      intro ε hε
      refine ⟨(s, w + ε / 2), ?_, ?_⟩
      · change goldenDisplacementCriticalBoundary s < w + ε / 2
        rw [hp]
        linarith
      · rw [dist_prod_same_left, Real.dist_eq, abs_of_nonpos (by linarith)]
        linarith
    · apply subset_closure
      change ¬ goldenDisplacementCriticalBoundary s < w
      linarith

end D5.S3.Analytic.Boundary.GoldenDisplacementConvergenceBoundary
