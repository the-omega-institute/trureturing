/- GID: D5/S3/Midline/HeatTraceConvergence
   generality: I
   mirror-B: D5/B/S3/Midline/HeatTraceConvergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact ordinary summability thresholds for heat coefficients. -/

import D5.S3.Midline.GoldenHeatBoundary
import D5.S3.Midline.ZetaHeatTraceBridge

/- Provenance: Native proof over pinned mathlib and frozen repository results. -/

namespace D5.S3.Midline.HeatTraceConvergence

open D5.S3.Midline.GoldenHeatBoundary
open D5.S3.Midline.GoldenHeatSpectrum
open D5.S3.Midline.UniversalHeatTrace
open D5.S3.Midline.ZetaHeatTraceBridge

/-- Boundary divergence makes the ordinary complex heat series summable exactly
to the right of its heat abscissa. -/
theorem heat_coefficient_summable_iff_of_boundary_divergent
    {A : Type*} (M : A → ℝ) (α : ℝ)
    (hAbscissa : BoundaryDivergentAbscissa M α) (s : ℂ) :
    Summable (heatCoefficient M s) ↔ α < s.re := by
  rw [← summable_norm_iff]
  simp_rw [heatCoefficient_norm]
  constructor
  · intro h
    rcases lt_trichotomy s.re α with hlt | heq | hgt
    · exact False.elim (hAbscissa.1.2 s.re hlt h)
    · exfalso
      apply hAbscissa.2
      simpa [heq] using h
    · exact hgt
  · intro hs
    exact hAbscissa.1.1 s.re hs

/-- The ordinary golden heat coefficients are summable exactly to the right of
the golden heat abscissa. -/
theorem golden_heat_coefficient_summable_iff (s : ℂ) :
    Summable (heatCoefficient goldenSpectrum s) ↔
      1 / Real.goldenRatio ^ 2 < s.re :=
  heat_coefficient_summable_iff_of_boundary_divergent
    goldenSpectrum (1 / Real.goldenRatio ^ 2) golden_heat_boundary_divergent s

/-- The ordinary prime-axis heat coefficients are summable exactly to the right
of one. -/
theorem prime_axis_heat_coefficient_summable_iff (s : ℂ) :
    Summable (heatCoefficient primeAxisLogLength s) ↔ 1 < s.re :=
  heat_coefficient_summable_iff_of_boundary_divergent
    primeAxisLogLength 1 primeAxisLogLength_boundary_divergent s

example : Summable (heatCoefficient primeAxisLogLength (2 : ℂ)) := by
  rw [prime_axis_heat_coefficient_summable_iff]
  norm_num

end D5.S3.Midline.HeatTraceConvergence
