/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipReflection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint Schwarz reflection of the native D-lip mean and regularized covariance. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipCovariance
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Schwarz reflection of the native signed D-lip germs. -/

open Complex Filter Set
open scoped Topology ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean

open OriginalFourMPeriodSource (dPeriod periodCorrection dPeriod_upper_reflection)
open OriginalFourMSlitMean (slitMean)
open OriginalGaussianExternalAnalyticCandidate (b)
open OriginalGaussianExternalSignedCandidate (h rho rationalT cauchy E K N G)

/-- The complex derivative reflects with the same lip exchange. -/
private theorem deriv_dPeriod_upper_reflection {t : ℝ} (ht : 1 < t) :
    deriv (dPeriod false) =ᶠ[𝓝 (t : ℂ)] fun r => conj (deriv (dPeriod true) (conj r)) := by
  have h := (dPeriod_upper_reflection ht).deriv
  rw [show (fun r => conj (dPeriod true (conj r))) = conj ∘ dPeriod true ∘ conj from rfl,
    deriv_conj_conj] at h
  exact h

/-- The logarithmic derivative in the actual D covariance reflects. -/
private theorem periodCorrection_dPeriod_upper_reflection {t : ℝ} (ht : 1 < t) :
    periodCorrection (dPeriod false) =ᶠ[𝓝 (t : ℂ)] fun r =>
      conj (periodCorrection (dPeriod true) (conj r)) := by
  filter_upwards [dPeriod_upper_reflection ht, deriv_dPeriod_upper_reflection ht] with r hP hP'
  simp only [periodCorrection, hP, hP', map_div₀, map_mul, map_sub, map_one, Complex.conj_conj]

private theorem invHalfPower_conj {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    (conj z) ^ (-1 / 2 : ℂ) = conj (z ^ (-1 / 2 : ℂ)) := by
  rw [Complex.conj_cpow _ _ (Complex.slitPlane_arg_ne_pi hz)]
  congr 2
  simp [map_ofNat]

private theorem b_conj (u : ℂ) : b (conj u) = conj (b u) := by simp [b]

private theorem h_conj (e : Bool) (u r : ℂ) :
    h e (conj u) (conj r) = conj (h e u r) := by cases e <;> simp [h]

/-- Reflection of the actual mean germ jointly in the local and D coordinates. -/
theorem dLipMean_upper_reflection (e : Bool) {t : ℝ} (ht : 1 < t) :
    (fun p : ℂ × ℂ => dLipMean false e p.1 p.2) =ᶠ[𝓝 (0, (t : ℂ))] fun p =>
      conj (dLipMean true e (conj p.1) (conj p.2)) := by
  let base (p : ℂ × ℂ) : ℂ :=
    if e then h e (conj p.1) (conj p.2) / b (conj p.1)
    else -(h e (conj p.1) (conj p.2) / b (conj p.1))
  have hbase : ContinuousAt base (0, (t : ℂ)) := by
    have hnum : ContinuousAt (fun p : ℂ × ℂ => h e (conj p.1) (conj p.2)) (0, (t : ℂ)) := by
      cases e <;> simp only [h, ite_true, ite_false, Bool.false_eq_true] <;> fun_prop
    have hden : ContinuousAt (fun p : ℂ × ℂ => b (conj p.1)) (0, (t : ℂ)) := by
      unfold b
      fun_prop
    have hq := hnum.div hden (by simp [b])
    cases e
    · exact hq.neg
    · exact hq
  have hpos : 0 < (base (0, (t : ℂ))).re := by
    cases e
    · simpa [base, h, b, sub_re] using sub_pos.mpr ht
    · simp [base, h, b]
  have hnear : ∀ᶠ p in 𝓝 (0, (t : ℂ)), base p ∈ Complex.slitPlane :=
    hbase.tendsto (isOpen_slitPlane.mem_nhds (Complex.mem_slitPlane_iff.mpr (Or.inl hpos)))
  filter_upwards [hnear] with p hp
  have hpow := invHalfPower_conj hp
  cases e
  · change dLipMean false false p.1 p.2 = conj (dLipMean true false (conj p.1) (conj p.2))
    change (b p.1)⁻¹ * (I * (-(h false p.1 p.2 / b p.1)) ^ (-1 / 2 : ℂ)) =
      conj ((b (conj p.1))⁻¹ *
        (-I * (-(h false (conj p.1) (conj p.2) / b (conj p.1))) ^ (-1 / 2 : ℂ)))
    simp only [base, Bool.false_eq_true, ite_false] at hpow
    rw [map_mul, map_mul, ← hpow]
    simp only [map_inv₀, map_neg, Complex.conj_I, neg_neg, b_conj, h_conj, map_div₀,
      Complex.conj_conj]
  · change slitMean true p.1 p.2 = conj (slitMean true (conj p.1) (conj p.2))
    simp only [base, ite_true] at hpow
    rw [slitMean, slitMean, map_mul, ← hpow]
    simp only [map_inv₀, b_conj, h_conj, map_div₀, Complex.conj_conj]

private theorem rho_conj (e f : Bool) (u v : ℂ) :
    rho e f (conj u) (conj v) = conj (rho e f u v) := by
  by_cases hef : e = f <;> simp [rho, hef]

private theorem cauchy_conj (e f : Bool) (u v : ℂ) :
    cauchy e f (conj u) (conj v) = conj (cauchy e f u v) := by
  by_cases hef : e = f <;> simp [cauchy, G, hef, rho_conj, map_ofNat]

private theorem rationalT_conj (e f : Bool) (u v r : ℂ) :
    rationalT e f (conj u) (conj v) (conj r) = conj (rationalT e f u v r) := by
  cases e <;> cases f <;> simp [rationalT, E, K, N, b, map_ofNat]

private theorem dLipCovariance_conj_of_means (l k e f : Bool) {u v r : ℂ}
    (hu : dLipMean false e u r = conj (dLipMean true e (conj u) (conj r)))
    (hv : dLipMean false f v r = conj (dLipMean true f (conj v) (conj r)))
    (hc : periodCorrection (dPeriod false) r =
      conj (periodCorrection (dPeriod true) (conj r))) :
    dLipCovariance false l k e f u v r =
      conj (dLipCovariance true l k e f (conj u) (conj v) (conj r)) := by
  let cov (u v r U V C : ℂ) :=
    if l = k then
      U * V * (r / 4 - C +
        r ^ 2 * rho e f u v / (4 * b u * b v * (h e u r * U + h f v r * V) ^ 2)) +
        (if e = f then 0 else cauchy e f u v)
    else -(U * V * (rationalT e f u v r - C))
  change cov u v r (dLipMean false e u r) (dLipMean false f v r)
      (periodCorrection (dPeriod false) r) =
    conj (cov (conj u) (conj v) (conj r) (dLipMean true e (conj u) (conj r))
      (dLipMean true f (conj v) (conj r)) (periodCorrection (dPeriod true) (conj r)))
  rw [hu, hv, hc]
  by_cases hlk : l = k
  · by_cases hef : e = f
    · simp only [cov, ite_eq_left hlk, ite_eq_left hef, add_zero, map_mul, map_add,
        map_sub, map_div₀, map_pow, map_ofNat, b_conj, h_conj, rho_conj, Complex.conj_conj]
    · simp only [cov, ite_eq_left hlk, ite_eq_right hef, map_mul, map_add, map_sub, map_div₀,
        map_pow, map_ofNat, b_conj, h_conj, rho_conj, cauchy_conj, Complex.conj_conj]
  · simp only [cov, ite_eq_right hlk, map_neg, map_mul, map_sub, rationalT_conj, Complex.conj_conj]

/-- Full covariance reflection jointly in the two local coordinates and the D
parameter. The formulas are totalized on both sides and keep the Cauchy term. -/
theorem dLipCovariance_upper_reflection_joint (l k e f : Bool) {t : ℝ} (ht : 1 < t) :
    (fun p : ℂ × ℂ × ℂ => dLipCovariance false l k e f p.1 p.2.1 p.2.2)
      =ᶠ[𝓝 (0, 0, (t : ℂ))] fun p =>
        conj (dLipCovariance true l k e f (conj p.1) (conj p.2.1) (conj p.2.2)) := by
  have hU : ContinuousAt (fun p : ℂ × ℂ × ℂ => (p.1, p.2.2)) (0, 0, (t : ℂ)) := by
    fun_prop
  have hV : ContinuousAt (fun p : ℂ × ℂ × ℂ => (p.2.1, p.2.2)) (0, 0, (t : ℂ)) := by
    fun_prop
  have hR : ContinuousAt (fun p : ℂ × ℂ × ℂ => p.2.2) (0, 0, (t : ℂ)) := by
    fun_prop
  filter_upwards [hU.tendsto.eventually (dLipMean_upper_reflection e ht),
    hV.tendsto.eventually (dLipMean_upper_reflection f ht),
    hR.tendsto.eventually (periodCorrection_dPeriod_upper_reflection ht)] with p hu hv hc
  exact dLipCovariance_conj_of_means l k e f hu hv hc

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean
