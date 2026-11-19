import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipMean
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitCovariance

/-! The original covariance on the local analytic continuation of the D lip. -/

open Complex Filter Set
open scoped Topology

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean

open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitPeriod)
open OriginalFourMPeriodSource (dLip dPeriod dPeriod_eq_slit periodCorrection)
open OriginalGaussianExternalAnalyticCandidate (b)
open OriginalGaussianExternalSignedCandidate (h rho rationalT cauchy E K N)
open OriginalFourMSlitMean (slitMean slitCovariance slitJ slitT)
open private dPeriod_analyticAt dPeriod_ne_zero deriv_dPeriod_eq
  from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPeriodSource
open private slitW mixedFree_joint
  from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitCovariance

private def dW (upperA e : Bool) (u r : ℂ) := h e u r * dLipMean upperA e u r

private def dCorrection (upperA : Bool) (r : ℂ) :=
  periodCorrection (dPeriod upperA) r

def dLipCovariance (upperA l k e f : Bool) (u v r : ℂ) : ℂ :=
  if l = k then
    dLipMean upperA e u r * dLipMean upperA f v r *
      (r / 4 - dCorrection upperA r +
        r ^ 2 * rho e f u v / (4 * b u * b v * (dW upperA e u r + dW upperA f v r) ^ 2)) +
      (if e = f then 0 else cauchy e f u v)
  else -(dLipMean upperA e u r * dLipMean upperA f v r *
    (rationalT e f u v r - dCorrection upperA r))

theorem dLipCovariance_eq_of_means (upperA l k e f : Bool) {r u v : ℂ}
    (hr : r ∈ dLip upperA)
    (hU : dLipMean upperA e u r = slitMean e u r)
    (hV : dLipMean upperA f v r = slitMean f v r) :
    dLipCovariance upperA l k e f u v r = slitCovariance l k e f u v r := by
  have hc : dCorrection upperA r = periodCorrection slitPeriod r := by
    unfold dCorrection periodCorrection
    rw [dPeriod_eq_slit hr, deriv_dPeriod_eq hr]
  simp only [dLipCovariance, slitCovariance, slitJ, slitT, dW, slitW, hU, hV, hc]

private abbrev Spatial := ℂ × ℂ × ℂ

attribute [local fun_prop] analyticAt_fst analyticAt_snd

private theorem rationalT_joint_at_d (e f : Bool) {t : ℝ} (ht : 1 < t) :
    AnalyticAt ℂ (fun p : Spatial => rationalT e f p.1 p.2.1 p.2.2) (0, 0, (t : ℂ)) := by
  have hE : AnalyticAt ℂ (fun p : Spatial => E e f p.1 p.2.1 p.2.2) (0, 0, (t : ℂ)) := by
    cases e <;> cases f <;> simp only [E, K, b, ite_true, ite_false, Bool.false_eq_true] <;>
      fun_prop
  have hN : AnalyticAt ℂ (fun p : Spatial => N e f p.1 p.2.1 p.2.2) (0, 0, (t : ℂ)) := by
    cases e <;> cases f <;> simp only [N, ite_true, ite_false, Bool.false_eq_true] <;> fun_prop
  have hn : 1 - (t : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ht.ne)
  have hE₀ : E e f 0 0 (t : ℂ) ≠ 0 := by cases e <;> cases f <;> simp [E, K, b, hn]
  have hr : AnalyticAt ℂ (fun p : Spatial => p.2.2) (0, 0, (t : ℂ)) := by fun_prop
  exact ((hr.mul hN).div (analyticAt_const.mul hE) (mul_ne_zero (by norm_num) hE₀)).add
    (((hr.pow 2).mul analyticAt_fst |>.mul (by fun_prop)).div (hE.pow 2) (pow_ne_zero 2 hE₀))

theorem dLipCovariance_joint_analytic (upperA l k e f : Bool) {t : ℝ} (ht : 1 < t) :
    AnalyticAt ℂ (fun p : Spatial => dLipCovariance upperA l k e f p.1 p.2.1 p.2.2)
      (0, 0, (t : ℂ)) := by
  have hL : AnalyticAt ℂ (fun p : Spatial => dLipMean upperA e p.1 p.2.2)
      (0, 0, (t : ℂ)) :=
    (dLipMean_joint_analytic upperA e ht).comp_of_eq
      (f := fun p : Spatial => (p.1, p.2.2)) (by fun_prop) rfl
  have hR : AnalyticAt ℂ (fun p : Spatial => dLipMean upperA f p.2.1 p.2.2)
      (0, 0, (t : ℂ)) :=
    (dLipMean_joint_analytic upperA f ht).comp_of_eq
      (f := fun p : Spatial => (p.2.1, p.2.2)) (by fun_prop) rfl
  have hPeriod := dPeriod_analyticAt upperA ht
  have hCorr : AnalyticAt ℂ (dCorrection upperA) (t : ℂ) :=
    (((analyticAt_id.mul (analyticAt_const.sub analyticAt_id)).mul hPeriod.deriv).div
      hPeriod (dPeriod_ne_zero upperA ht))
  have hc : AnalyticAt ℂ (fun p : Spatial => dCorrection upperA p.2.2) (0, 0, (t : ℂ)) :=
    hCorr.comp_of_eq (f := fun p : Spatial => p.2.2) (by fun_prop) rfl
  by_cases hlk : l = k
  · have hWL : AnalyticAt ℂ (fun p : Spatial => dW upperA e p.1 p.2.2) (0, 0, (t : ℂ)) := by
      apply AnalyticAt.mul _ hL
      cases e <;> simp only [h, ite_true, ite_false, Bool.false_eq_true] <;> fun_prop
    have hWR : AnalyticAt ℂ (fun p : Spatial => dW upperA f p.2.1 p.2.2) (0, 0, (t : ℂ)) := by
      apply AnalyticAt.mul _ hR
      cases f <;> simp only [h, ite_true, ite_false, Bool.false_eq_true] <;> fun_prop
    have hn : 4 * b 0 * b 0 * (dW upperA e 0 t + dW upperA f 0 t) ^ 2 ≠ 0 := by
      simpa [b, dW] using mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0)
        (pow_ne_zero 2 (dLipWeighted_sum_ne_zero upperA e f ht))
    have hden : AnalyticAt ℂ (fun p : Spatial =>
        4 * b p.1 * b p.2.1 * (dW upperA e p.1 p.2.2 + dW upperA f p.2.1 p.2.2) ^ 2)
        (0, 0, (t : ℂ)) :=
      (by unfold b; fun_prop : AnalyticAt ℂ (fun p : Spatial => 4 * b p.1 * b p.2.1)
        (0, 0, (t : ℂ))).mul ((hWL.add hWR).pow 2)
    have hnum : AnalyticAt ℂ (fun p : Spatial => p.2.2 ^ 2 * rho e f p.1 p.2.1)
        (0, 0, (t : ℂ)) := by
      by_cases hef : e = f <;> simp only [rho, hef, ite_true, ite_false] <;> fun_prop
    simp only [dLipCovariance, hlk, ite_true]
    exact ((hL.mul hR).mul (((by fun_prop : AnalyticAt ℂ (fun p : Spatial => p.2.2 / 4)
        (0, 0, (t : ℂ))).sub hc).add (hnum.div hden hn))).add (mixedFree_joint e f _)
  · simp only [dLipCovariance, hlk, ite_false]
    exact ((hL.mul hR).mul ((rationalT_joint_at_d e f ht).sub hc)).neg

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean
