/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Principal-branch continuation of the signed native half-current source. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedOverlap
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Principal-branch continuation of the signed native half-current source. -/

set_option maxRecDepth 4096

noncomputable section

open Complex Set Filter
open scoped Topology

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSlitMean

open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
open OriginalGaussianExternalAnalyticCandidate (b correction)
open OriginalGaussianExternalGenerators (sourceMode)
open OriginalGaussianExternalSignedCandidate (h normalizedArgument)
open OriginalFourMPeriodSource (periodCorrection)
open private source_closed from D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource
open private sqrt_re_pos from D5.S3.Analytic.OriginalHalfBinomialSlitPeriod

/-- The native half-current source in its principal binomial branch. -/
def slitMean (e : Bool) (u r : ℂ) : ℂ :=
  (b u)⁻¹ * (h e u r / b u) ^ (-1 / 2 : ℂ)

theorem slitMean_eq_sourceMode (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) :
    slitMean e u r = sourceMode e u r := by
  have hb : b u ≠ 0 := (OriginalGaussianExternalModeSums.mode_factors_ne_zero hu).1
  have hratio : h e u r / b u = normalizedArgument e u r := by
    cases e <;> simp only [h, normalizedArgument, Bool.false_eq_true, ite_false,
      ite_true] <;> field_simp [hb] <;> unfold b <;> ring
  rw [source_closed e hu, slitMean, one_div, hratio]

private theorem sourceArgument_zero_mem (e : Bool) {r : ℂ} (hr : r ∈ slitDomain) :
    h e 0 r / b 0 ∈ Complex.slitPlane := by
  cases e
  · simpa [h, b, slitDomain] using hr
  · simp [h, b]

theorem slitMean_joint_analytic (e : Bool) {r : ℂ} (hr : r ∈ slitDomain) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => slitMean e p.1 p.2) (0, r) := by
  have hb : AnalyticAt ℂ (fun p : ℂ × ℂ => b p.1) (0, r) :=
    analyticAt_const.sub analyticAt_fst
  have hn : b 0 ≠ 0 := by simp [b]
  have hh : AnalyticAt ℂ (fun p : ℂ × ℂ => h e p.1 p.2) (0, r) := by
    cases e
    · exact (analyticAt_const.sub analyticAt_snd).sub analyticAt_fst
    · exact analyticAt_const.sub ((analyticAt_const.sub analyticAt_snd).mul analyticAt_fst)
  exact (hb.inv hn).mul ((hh.div hb hn).cpow analyticAt_const (sourceArgument_zero_mem e hr))

/-- At the external Taylor centre the two regularized same-slot half factors
have strictly positive real parts. -/
theorem slitMean_weighted_re_pos (e : Bool) {r : ℂ} (hr : r ∈ slitDomain) :
    0 < (h e 0 r * slitMean e 0 r).re := by
  cases e
  · have hn : 1 - r ≠ 0 := slitPlane_ne_zero hr
    have he : (1 - r) * (1 - r) ^ (-1 / 2 : ℂ) = (1 - r) ^ (1 / 2 : ℂ) := by
      calc
        _ = (1 - r) ^ ((1 : ℂ) + (-1 / 2 : ℂ)) := by
          rw [cpow_add _ _ hn, cpow_one]
        _ = _ := by norm_num
    simp only [h, b, Bool.false_eq_true, ite_false, sub_zero, slitMean,
      inv_one, one_mul, div_one, he]
    exact sqrt_re_pos hr
  · simp [h, b, slitMean]

theorem slitPeriodCorrection_analyticOnNhd :
    AnalyticOnNhd ℂ (periodCorrection slitPeriod) slitDomain := by
  intro r hr
  have hP := slitPeriod_analyticOnNhd _ hr
  exact (((analyticAt_id.mul (analyticAt_const.sub analyticAt_id)).mul hP.deriv).div
    hP (slitPeriod_ne_zero hr))

#print axioms slitMean_eq_sourceMode
#print axioms slitMean_joint_analytic
#print axioms slitMean_weighted_re_pos
#print axioms slitPeriodCorrection_analyticOnNhd

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSlitMean
