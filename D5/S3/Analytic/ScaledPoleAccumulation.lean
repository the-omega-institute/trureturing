/- GID: D5/S3/Analytic/ScaledPoleAccumulation
   generality: G
   mirror-B: D5/B/S3/Analytic/ScaledPoleAccumulation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Scaled candidate poles converge to any targeted point on the imaginary axis. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace D5.S3.Analytic.ScaledPoleAccumulation

open Complex Filter Topology

/-- If the positive scale tends to infinity and the normalized heights tend
to a real target, then the associated candidate poles converge to that point
on the imaginary axis. The hypotheses expose the zero-height approximation
input used by the source atom; this theorem supplies the reusable scaling
limit and does not assert that input for any particular analytic function. -/
theorem scaled_candidate_poles_tendsto
    (scale height : ℕ → ℝ) (target : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hheight : Tendsto (fun n => height n / scale n) atTop (𝓝 target)) :
    Tendsto
      (fun n =>
        (((2 * scale n)⁻¹ : ℝ) : ℂ) +
          ((height n / scale n : ℝ) : ℂ) * I)
      atTop (𝓝 ((target : ℂ) * I)) := by
  have hinv : Tendsto (fun n => (scale n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hscale
  have hreal : Tendsto (fun n => (2 * scale n)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa [mul_inv_rev, mul_comm] using hinv.const_mul (2 : ℝ)⁻¹
  have hrealComplex :
      Tendsto (fun n => (((2 * scale n)⁻¹ : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) :=
    tendsto_ofReal_iff.mpr hreal
  have hheightComplex :
      Tendsto (fun n => ((height n / scale n : ℝ) : ℂ)) atTop
        (𝓝 (target : ℂ)) :=
    tendsto_ofReal_iff.mpr hheight
  simpa using hrealComplex.add (hheightComplex.mul_const I)

end D5.S3.Analytic.ScaledPoleAccumulation
