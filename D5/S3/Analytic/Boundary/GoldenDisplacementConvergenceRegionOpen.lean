/- GID: D5/S3/Analytic/Boundary/GoldenDisplacementConvergenceRegionOpen
   generality: I
   mirror-B: D5/B/S3/Analytic/Boundary/GoldenDisplacementConvergenceRegionOpen
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden displacement convergence region is an open subset of the parameter plane. -/

/- Library-search audit trail (2026-08-26):
   * Repository searches over D5/**/*.lean and Blueprint/**/*.scribe.cs plus Blueprint/**/*.md
     found no IsOpen declaration for the golden displacement convergence region and no theorem
     connecting Summable (dTerm ...) to a topological predicate.
   * The existing repository theorem dTerm_summable_iff_two_constraints supplies the exact
     two strict affine inequalities used below; GoldenDisplacementRegionConvexity supplies only
     Convexity and is not imported because it is not needed for this topological consequence.
   * Pinned Mathlib supplies isOpen_lt and the fun_prop continuity prover for affine maps on
     the product parameter space. No separate region definition was found or introduced.
-/

import D5.S3.Analytic.Displacement.GoldenDisplacementTwoConstraintRegion

set_option autoImplicit false
set_option relaxedAutoImplicit false

open GoldenDisplacementEulerProduct
open GoldenDisplacementTwoConstraintRegion

namespace D5.S3.Analytic.Boundary.GoldenDisplacementConvergenceRegionOpen

theorem golden_displacement_convergence_region_open :
    IsOpen {p : ℝ × ℝ | Summable (dTerm p.1 p.2)} := by
  have hfirst : IsOpen {p : ℝ × ℝ | 1 < 2 * p.1 + p.2} := by
    exact isOpen_lt (by fun_prop) (by fun_prop)
  have hsecond : IsOpen {p : ℝ × ℝ | 1 < 3 * p.1 + 2 * p.2} := by
    exact isOpen_lt (by fun_prop) (by fun_prop)
  have hregion :
      {p : ℝ × ℝ | Summable (dTerm p.1 p.2)} =
        {p : ℝ × ℝ | 1 < 2 * p.1 + p.2} ∩
          {p : ℝ × ℝ | 1 < 3 * p.1 + 2 * p.2} := by
    ext p
    change Summable (dTerm p.1 p.2) ↔
      (1 < 2 * p.1 + p.2 ∧ 1 < 3 * p.1 + 2 * p.2)
    exact dTerm_summable_iff_two_constraints p.1 p.2
  rw [hregion]
  exact hfirst.inter hsecond

end D5.S3.Analytic.Boundary.GoldenDisplacementConvergenceRegionOpen
