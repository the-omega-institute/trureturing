/- GID: D5/S3/Analytic/Dilation/ScalarUnitDressing
   generality: G
   mirror-B: D5/B/S3/Analytic/Dilation/ScalarUnitDressing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonvanishing analytic scalar dressing preserves zeros and their multiplicities. -/

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic

/- Library-search and duplication audit (2026-09-04):
   * Repository searches covered scalar dressing, nonvanishing factors, zero
     responses, zero divisors, and analytic orders. `ScaleShapeSeparation` proves
     a spectrum-specific zero-set statement, but no public D5 theorem gives the
     generic analytic zero-and-multiplicity result below.
   * The formalization-receipt and digestion indexes have no binding for the
     source atom. The in-flight branch scan found no competing deposit.
   * Pinned Mathlib supplies `mul_eq_zero_iff_left`, `analyticOrderAt_mul`, and
     `AnalyticAt.analyticOrderAt_eq_zero`; the proof uses them directly.
   * Pointwise nonvanishing alone preserves the zero predicate. Analyticity of
     both factors is added explicitly because the source also claims unchanged
     zero multiplicity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Dilation.ScalarUnitDressing

/-- Multiplication by a scalar factor that is analytic and nonzero at `s`
preserves both vanishing at `s` and the analytic order there. -/
theorem nonzero_scalar_dressing_preserves_zero_and_analytic_order
    {f g : ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f s) (hg : AnalyticAt ℂ g s) (hg0 : g s ≠ 0) :
    (g s * f s = 0 ↔ f s = 0) ∧
      analyticOrderAt (fun z => g z * f z) s = analyticOrderAt f s := by
  constructor
  · exact mul_eq_zero_iff_left hg0
  · change analyticOrderAt (g * f) s = analyticOrderAt f s
    rw [analyticOrderAt_mul hg hf, hg.analyticOrderAt_eq_zero.mpr hg0, zero_add]

#print axioms nonzero_scalar_dressing_preserves_zero_and_analytic_order

end D5.S3.Analytic.Dilation.ScalarUnitDressing
