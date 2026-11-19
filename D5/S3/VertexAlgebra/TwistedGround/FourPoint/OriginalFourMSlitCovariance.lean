/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Holomorphic extension of the signed same-leg and opposite-leg Gaussian kernels. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitMean

/-! Holomorphic extension of the signed same-leg and opposite-leg Gaussian kernels. -/

set_option maxRecDepth 4096

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSlitMean

open Set Filter
open scoped Topology
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
open OriginalGaussianExternalAnalyticCandidate (b)
open OriginalGaussianExternalSignedCandidate (h W rho K E N G cauchy rationalT)
open OriginalFourMPeriodSource (periodCorrection)
open OriginalFourMSignedOverlap (covarianceMode)
open private slit_correction_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedOverlap

private def slitW (e : Bool) (u r : ℂ) : ℂ := h e u r * slitMean e u r

/-- The signed same-leg Gaussian on the Euler slit. -/
def slitJ (e f : Bool) (u v r : ℂ) : ℂ :=
  slitMean e u r * slitMean f v r *
    (r / 4 - periodCorrection slitPeriod r +
      r ^ 2 * rho e f u v / (4 * b u * b v * (slitW e u r + slitW f v r) ^ 2))

/-- The signed opposite-leg Gaussian on the Euler slit. -/
def slitT (e f : Bool) (u v r : ℂ) : ℂ :=
  slitMean e u r * slitMean f v r * (rationalT e f u v r - periodCorrection slitPeriod r)

/-- The continued signed matrix generator, including the mixed free entry. -/
def slitCovariance (l k e f : Bool) (u v r : ℂ) : ℂ :=
  if l = k then slitJ e f u v r + (if e = f then 0 else cauchy e f u v)
  else -slitT e f u v r

theorem slitCovariance_eq_native (l k e f : Bool) {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) :
    slitCovariance l k e f u v r = covarianceMode l k e f u v r := by
  have hr : ‖r‖ < 1 := by linarith [norm_nonneg u]
  simp only [slitCovariance, covarianceMode, slitJ, slitT, slitW,
    OriginalGaussianExternalSignedCandidate.candidateJ,
    OriginalGaussianExternalSignedCandidate.candidateT, W,
    slitMean_eq_sourceMode e hu, slitMean_eq_sourceMode f hv, slit_correction_eq hr]

attribute [local fun_prop] analyticAt_fst analyticAt_snd

private abbrev Spatial := ℂ × ℂ × ℂ

private theorem rationalT_joint (e f : Bool) {r : ℂ} (hr : r ∈ slitDomain) :
    AnalyticAt ℂ (fun p : Spatial => rationalT e f p.1 p.2.1 p.2.2) (0, 0, r) := by
  have hE : AnalyticAt ℂ (fun p : Spatial => E e f p.1 p.2.1 p.2.2) (0, 0, r) := by
    cases e <;> cases f <;> simp only [E, K, b, ite_true, ite_false, Bool.false_eq_true] <;>
      fun_prop
  have hN : AnalyticAt ℂ (fun p : Spatial => N e f p.1 p.2.1 p.2.2) (0, 0, r) := by
    cases e <;> cases f <;> simp only [N, ite_true, ite_false, Bool.false_eq_true] <;> fun_prop
  have hE0 : E e f 0 0 r ≠ 0 := by
    have hn : 1 - r ≠ 0 := Complex.slitPlane_ne_zero hr
    cases e <;> cases f <;> simp [E, K, b, hn]
  have hR : AnalyticAt ℂ (fun p : Spatial => p.2.2) (0, 0, r) := by fun_prop
  exact ((hR.mul hN).div (analyticAt_const.mul hE) (mul_ne_zero (by norm_num) hE0)).add
    (((hR.pow 2).mul analyticAt_fst |>.mul (by fun_prop)).div (hE.pow 2) (pow_ne_zero 2 hE0))

private theorem mixedFree_joint (e f : Bool) (r : ℂ) :
    AnalyticAt ℂ (fun p : Spatial => if e = f then 0 else cauchy e f p.1 p.2.1)
      (0, 0, r) := by
  by_cases hef : e = f
  · simp [hef, analyticAt_const]
  · simp only [hef, ite_false, cauchy, G, rho]
    exact (by fun_prop : AnalyticAt ℂ (fun p : Spatial => -(1 + p.1 * p.2.1)) (0, 0, r)).div
      (by fun_prop) (by norm_num)

theorem slitCovariance_joint_analytic (l k e f : Bool) {r : ℂ} (hr : r ∈ slitDomain) :
    AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => slitCovariance l k e f p.1 p.2.1 p.2.2) (0, 0, r) := by
  have hL : AnalyticAt ℂ (fun p : Spatial => slitMean e p.1 p.2.2) (0, 0, r) :=
    (slitMean_joint_analytic e hr).comp_of_eq
      (f := fun p : Spatial => (p.1, p.2.2)) (by fun_prop) rfl
  have hR : AnalyticAt ℂ (fun p : Spatial => slitMean f p.2.1 p.2.2) (0, 0, r) :=
    (slitMean_joint_analytic f hr).comp_of_eq
      (f := fun p : Spatial => (p.2.1, p.2.2)) (by fun_prop) rfl
  have hc : AnalyticAt ℂ (fun p : Spatial => periodCorrection slitPeriod p.2.2) (0, 0, r) :=
    (slitPeriodCorrection_analyticOnNhd r hr).comp_of_eq
      (f := fun p : Spatial => p.2.2) (by fun_prop) rfl
  by_cases hlk : l = k
  · have hWL : AnalyticAt ℂ (fun p : Spatial => slitW e p.1 p.2.2) (0, 0, r) := by
      apply AnalyticAt.mul _ hL
      cases e <;> simp only [h, ite_true, ite_false, Bool.false_eq_true] <;> fun_prop
    have hWR : AnalyticAt ℂ (fun p : Spatial => slitW f p.2.1 p.2.2) (0, 0, r) := by
      apply AnalyticAt.mul _ hR
      cases f <;> simp only [h, ite_true, ite_false, Bool.false_eq_true] <;> fun_prop
    have hW : slitW e 0 r + slitW f 0 r ≠ 0 := by
      intro hz
      have hpos := add_pos (slitMean_weighted_re_pos e hr) (slitMean_weighted_re_pos f hr)
      change 0 < (slitW e 0 r).re + (slitW f 0 r).re at hpos
      rw [← Complex.add_re, hz, Complex.zero_re] at hpos
      exact lt_irrefl _ hpos
    have hn : 4 * b 0 * b 0 * (slitW e 0 r + slitW f 0 r) ^ 2 ≠ 0 := by
      simpa [b] using mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (pow_ne_zero 2 hW)
    have hden : AnalyticAt ℂ
        (fun p : Spatial => 4 * b p.1 * b p.2.1 * (slitW e p.1 p.2.2 + slitW f p.2.1 p.2.2) ^ 2)
        (0, 0, r) := by
      exact (by unfold b; fun_prop : AnalyticAt ℂ (fun p : Spatial => 4 * b p.1 * b p.2.1)
        (0, 0, r)).mul ((hWL.add hWR).pow 2)
    have hnum : AnalyticAt ℂ
        (fun p : Spatial => p.2.2 ^ 2 * rho e f p.1 p.2.1) (0, 0, r) := by
      by_cases hef : e = f <;> simp only [rho, hef, ite_true, ite_false] <;> fun_prop
    simp only [slitCovariance, hlk, ite_true, slitJ]
    exact ((hL.mul hR).mul (((by fun_prop : AnalyticAt ℂ
      (fun p : Spatial => p.2.2 / 4) (0, 0, r)).sub hc).add
        (hnum.div hden hn))).add (mixedFree_joint e f r)
  · simp only [slitCovariance, hlk, ite_false, slitT]
    exact ((hL.mul hR).mul ((rationalT_joint e f hr).sub hc)).neg

#print axioms slitCovariance_eq_native
#print axioms slitCovariance_joint_analytic

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSlitMean
