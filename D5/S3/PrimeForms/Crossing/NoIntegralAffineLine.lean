/- GID: D5/S3/PrimeForms/Crossing/NoIntegralAffineLine
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Crossing/NoIntegralAffineLine
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The crossing quadratic surface contains no nonconstant integral affine line. -/

/- Library-search audit trail (2026-08-17):
   * No equivalent declaration was found in D5.
   * Pinned-Mathlib source search and `smart_search.sh` found no theorem for
     this quadratic surface or its integral affine lines.
   * LeanSearch returned only generic affine-line and quadratic-map results,
     including `AffineMap.lineMap_eq_lineMap_iff` and
     `QuadraticMap.PosDef.anisotropic`; neither proves this indefinite case.
   * Loogle rejected the natural-language query as an unknown identifier, and
     unauthenticated GitHub code search returned HTTP 401.
-/

import Mathlib.Tactic

namespace D5.S3.PrimeForms.Crossing.NoIntegralAffineLine

/-- The integral surface `b^2 - b*c + c^2 - t^2 = -1` contains no
nonconstant affine line with integral base point and direction. -/
theorem crossing_surface_has_no_nonconstant_integral_affine_line
    (b c t u v w : Int)
    (hline : ∀ n : Int,
      (b + n * u) ^ 2 - (b + n * u) * (c + n * v) + (c + n * v) ^ 2 -
          (t + n * w) ^ 2 = -1) :
    u = 0 ∧ v = 0 ∧ w = 0 := by
  have hzero := hline 0
  have hone := hline 1
  have hneg := hline (-1)
  have hpoint : b ^ 2 - b * c + c ^ 2 - t ^ 2 = -1 := by
    simpa using hzero
  have hdirection : u ^ 2 - u * v + v ^ 2 - w ^ 2 = 0 := by
    nlinarith [hone, hneg, hzero]
  have horth :
      2 * b * u - b * v - c * u + 2 * c * v - 2 * t * w = 0 := by
    nlinarith [hone, hneg]
  have hqv : u ^ 2 - u * v + v ^ 2 = w ^ 2 := by
    nlinarith [hdirection]
  have hbilinear : 2 * b * u - b * v - c * u + 2 * c * v = 2 * t * w := by
    nlinarith [horth]
  have hgram :
      4 * (b ^ 2 - b * c + c ^ 2) * (u ^ 2 - u * v + v ^ 2) -
          (2 * b * u - b * v - c * u + 2 * c * v) ^ 2 =
        3 * (b * v - c * u) ^ 2 := by
    ring
  have hkey :
      4 * w ^ 2 * (b ^ 2 - b * c + c ^ 2 - t ^ 2) =
        3 * (b * v - c * u) ^ 2 := by
    calc
      4 * w ^ 2 * (b ^ 2 - b * c + c ^ 2 - t ^ 2) =
          4 * (b ^ 2 - b * c + c ^ 2) * (u ^ 2 - u * v + v ^ 2) -
            (2 * b * u - b * v - c * u + 2 * c * v) ^ 2 := by
              rw [hqv, hbilinear]
              ring
      _ = 3 * (b * v - c * u) ^ 2 := hgram
  rw [hpoint] at hkey
  have hw_sq : w ^ 2 = 0 := by
    nlinarith only [hkey, sq_nonneg (b * v - c * u)]
  have hw : w = 0 := sq_eq_zero_iff.mp hw_sq
  have hdir0 : u ^ 2 - u * v + v ^ 2 = 0 := by
    simpa [hw] using hdirection
  have hsquares : (2 * u - v) ^ 2 + 3 * v ^ 2 = 0 := by
    nlinarith only [hdir0]
  have hv_sq : v ^ 2 = 0 := by
    nlinarith only [hsquares, sq_nonneg (2 * u - v), sq_nonneg v]
  have hv : v = 0 := sq_eq_zero_iff.mp hv_sq
  have hu_sq : u ^ 2 = 0 := by
    simpa [hv] using hdir0
  have hu : u = 0 := sq_eq_zero_iff.mp hu_sq
  exact ⟨hu, hv, hw⟩

#print axioms crossing_surface_has_no_nonconstant_integral_affine_line

end D5.S3.PrimeForms.Crossing.NoIntegralAffineLine
