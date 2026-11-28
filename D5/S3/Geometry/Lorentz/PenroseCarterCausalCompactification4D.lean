/- GID: D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conformal boundaries, Kruskal extension and sharp interior proper time. -/

import OmegaBuild.Commands
import D5.S3.Analysis.ExponentialRadialCoordinates
import D5.S3.Analysis.SymmetricAngleCoordinates
import D5.S3.Geometry.Lorentz.FLRWCosmologyFriedmann4D
import D5.S3.Geometry.Lorentz.BlackHoleThermodynamics4D
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-! Exact spherical coordinate charts and causal metric identities. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Real Set Filter
open scoped Topology
namespace D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D

def minkowskiT (t r : ℝ) : ℝ := arctan (t + r) + arctan (t - r)
def minkowskiR (t r : ℝ) : ℝ := arctan (t + r) - arctan (t - r)
def conformalFactor (T R : ℝ) : ℝ := cos T + cos R
def diamond (T R : ℝ) : Prop := 0 ≤ R ∧ |T| + R < π
def inverseTime (T R : ℝ) : ℝ := sin T / conformalFactor T R
def inverseRadius (T R : ℝ) : ℝ := sin R / conformalFactor T R

open OmegaMath.SymmetricAngleCoordinates (half_angle_bounds cosineSum_add_sub sineQuotient_add_sub)

private theorem factor_add_sub (a b : ℝ) :
    conformalFactor (a + b) (a - b) = 2 * cos a * cos b := cosineSum_add_sub a b

theorem minkowski_image {t r : ℝ} (hr : 0 ≤ r) :
    diamond (minkowskiT t r) (minkowskiR t r) := by
  have hm := arctan_mono (show t - r ≤ t + r by linarith)
  have h₁ := arctan_lt_pi_div_two (t + r)
  have h₂ := neg_pi_div_two_lt_arctan (t - r)
  refine ⟨sub_nonneg.mpr hm, ?_⟩
  unfold minkowskiT minkowskiR
  rw [← lt_sub_iff_add_lt, abs_lt]
  constructor <;> linarith

theorem conformalFactor_pos {T R : ℝ} (h : diamond T R) :
    0 < conformalFactor T R := by
  obtain ⟨ha, hb, hc, hd⟩ := half_angle_bounds h.1 h.2
  have hfac : conformalFactor T R =
      conformalFactor ((T + R) / 2 + (T - R) / 2) ((T + R) / 2 - (T - R) / 2) := by
    congr 1 <;> ring
  rw [hfac, factor_add_sub]
  exact mul_pos (mul_pos (by norm_num) (cos_pos_of_mem_Ioo ⟨ha, hb⟩))
    (cos_pos_of_mem_Ioo ⟨hc, hd⟩)

private theorem inverse_add_sub {a b : ℝ} (ha : cos a ≠ 0) (hb : cos b ≠ 0) :
    inverseTime (a + b) (a - b) = (tan a + tan b) / 2 ∧
    inverseRadius (a + b) (a - b) = (tan a - tan b) / 2 := by
  simpa only [OmegaMath.SymmetricAngleCoordinates.sineQuotient,
    OmegaMath.SymmetricAngleCoordinates.cosineSum, inverseTime, inverseRadius, conformalFactor,
    add_comm (cos (a - b))] using sineQuotient_add_sub ha hb

theorem minkowski_inverse (t r : ℝ) :
    inverseTime (minkowskiT t r) (minkowskiR t r) = t ∧
    inverseRadius (minkowskiT t r) (minkowskiR t r) = r := by
  have h := inverse_add_sub (cos_arctan_pos (t + r)).ne'
    (cos_arctan_pos (t - r)).ne'
  simpa [minkowskiT, minkowskiR, tan_arctan, add_div, sub_div] using h

theorem minkowski_onto {T R : ℝ} (h : diamond T R) :
    0 ≤ inverseRadius T R ∧
    minkowskiT (inverseTime T R) (inverseRadius T R) = T ∧
    minkowskiR (inverseTime T R) (inverseRadius T R) = R := by
  obtain ⟨ha, hb, hc, hd⟩ := half_angle_bounds h.1 h.2
  have he : T = (T + R) / 2 + (T - R) / 2 := by ring
  have hf : R = (T + R) / 2 - (T - R) / 2 := by ring
  have hi := inverse_add_sub (cos_pos_of_mem_Ioo ⟨ha, hb⟩).ne'
    (cos_pos_of_mem_Ioo ⟨hc, hd⟩).ne'
  rw [← he, ← hf] at hi
  have hs : 0 ≤ sin R := sin_nonneg_of_mem_Icc ⟨h.1, by
    have := abs_nonneg T; linarith [h.2]⟩
  refine ⟨div_nonneg hs (conformalFactor_pos h).le, ?_⟩
  have hp : inverseTime T R + inverseRadius T R = tan ((T + R) / 2) := by
    rw [hi.1, hi.2]; ring
  have hm : inverseTime T R - inverseRadius T R = tan ((T - R) / 2) := by
    rw [hi.1, hi.2]; ring
  simp only [minkowskiT, minkowskiR, hp, hm, arctan_tan ha hb, arctan_tan hc hd]
  constructor <;> ring

theorem minkowski_image_iff (T R : ℝ) :
    diamond T R ↔ ∃ t r : ℝ, 0 ≤ r ∧ minkowskiT t r = T ∧ minkowskiR t r = R := by
  constructor
  · intro h
    exact ⟨_, _, minkowski_onto h⟩
  · rintro ⟨t, r, hr, rfl, rfl⟩
    exact minkowski_image hr

def angularSpeedSq (θ θ' φ' : ℝ) : ℝ := θ' ^ 2 + sin θ ^ 2 * φ' ^ 2
def minkowskiMetric (r θ dt dr dθ dφ : ℝ) : ℝ :=
  -dt ^ 2 + dr ^ 2 + r ^ 2 * angularSpeedSq θ dθ dφ
def cylinderMetric (R θ dT dR dθ dφ : ℝ) : ℝ :=
  -dT ^ 2 + dR ^ 2 + sin R ^ 2 * angularSpeedSq θ dθ dφ

theorem minkowski_coordinate_derivatives {t r : ℝ → ℝ} {s dt dr : ℝ}
    (ht : HasDerivAt t dt s) (hr : HasDerivAt r dr s) :
    HasDerivAt (fun x => minkowskiT (t x) (r x))
      ((dt + dr) / (1 + (t s + r s)^2) + (dt - dr) / (1 + (t s - r s)^2)) s ∧
    HasDerivAt (fun x => minkowskiR (t x) (r x))
      ((dt + dr) / (1 + (t s + r s)^2) - (dt - dr) / (1 + (t s - r s)^2)) s := by
  have hp := (ht.add hr).arctan
  have hm := (ht.sub hr).arctan
  constructor
  · convert hp.add hm using 1 <;> first | rfl | simp only [Pi.add_apply, Pi.sub_apply]; ring
  · convert hp.sub hm using 1 <;> first | rfl | simp only [Pi.add_apply, Pi.sub_apply]; ring

private theorem minkowski_factor_sq (t r : ℝ) :
    conformalFactor (minkowskiT t r) (minkowskiR t r)^2 =
      4 / ((1 + (t + r)^2) * (1 + (t - r)^2)) := by
  rw [minkowskiT, minkowskiR, factor_add_sub]
  rw [mul_pow, mul_pow, cos_sq_arctan, cos_sq_arctan]
  field_simp
  ring

theorem minkowski_metric_pullback (t r θ dt dr dθ dφ : ℝ) :
    conformalFactor (minkowskiT t r) (minkowskiR t r)^2 *
      minkowskiMetric r θ dt dr dθ dφ =
    cylinderMetric (minkowskiR t r) θ
      ((dt + dr) / (1 + (t + r)^2) + (dt - dr) / (1 + (t - r)^2))
      ((dt + dr) / (1 + (t + r)^2) - (dt - dr) / (1 + (t - r)^2)) dθ dφ := by
  have hp : 1 + (t + r)^2 ≠ 0 := ne_of_gt (by positivity)
  have hm : 1 + (t - r)^2 ≠ 0 := ne_of_gt (by positivity)
  have ho : conformalFactor (minkowskiT t r) (minkowskiR t r) ≠ 0 := by
    rw [minkowskiT, minkowskiR, factor_add_sub]
    exact (mul_pos (mul_pos (by norm_num) (cos_arctan_pos _)) (cos_arctan_pos _)).ne'
  have hs := (div_eq_iff ho).mp (minkowski_inverse t r).2
  have hs₂ : sin (minkowskiR t r)^2 = r^2 *
      conformalFactor (minkowskiT t r) (minkowskiR t r)^2 := by rw [hs]; ring
  unfold minkowskiMetric cylinderMetric
  rw [hs₂, minkowski_factor_sq]
  field_simp
  ring

theorem minkowski_curve_pullback {t r θ φ : ℝ → ℝ} {s dt dr dθ dφ : ℝ}
    (ht : HasDerivAt t dt s) (hr : HasDerivAt r dr s)
    (hθ : HasDerivAt θ dθ s) (hφ : HasDerivAt φ dφ s) :
    conformalFactor (minkowskiT (t s) (r s)) (minkowskiR (t s) (r s))^2 *
      minkowskiMetric (r s) (θ s) dt dr dθ dφ =
    cylinderMetric (minkowskiR (t s) (r s)) (θ s)
      (deriv (fun x => minkowskiT (t x) (r x)) s)
      (deriv (fun x => minkowskiR (t x) (r x)) s) (deriv θ s) (deriv φ s) := by
  obtain ⟨hT, hR⟩ := minkowski_coordinate_derivatives ht hr
  rw [hT.deriv, hR.deriv, hθ.deriv, hφ.deriv]
  exact minkowski_metric_pullback _ _ _ _ _ _ _

theorem minkowski_conformal_metric_pullback {T R : ℝ → ℝ} {s dT dR : ℝ}
    (ht : HasDerivAt T dT s) (hr : HasDerivAt R dR s) (h : diamond (T s) (R s)) (w : ℝ) :
    -deriv (fun x => inverseTime (T x) (R x)) s ^ 2 +
      deriv (fun x => inverseRadius (T x) (R x)) s ^ 2 + inverseRadius (T s) (R s) ^ 2 * w ^ 2 =
      (conformalFactor (T s) (R s))⁻¹ ^ 2 * (-dT ^ 2 + dR ^ 2 + sin (R s) ^ 2 * w ^ 2) := by
  simpa only [OmegaMath.SymmetricAngleCoordinates.sineQuotient,
    OmegaMath.SymmetricAngleCoordinates.cosineSum, inverseTime, inverseRadius, conformalFactor,
    add_comm (cos (R _))] using
    OmegaMath.SymmetricAngleCoordinates.symmetric_derivative_difference ht hr h.1 h.2 w

theorem conformalFactor_derivative {T R : ℝ → ℝ} {s dT dR : ℝ}
    (hT : HasDerivAt T dT s) (hR : HasDerivAt R dR s) :
    HasDerivAt (fun x => conformalFactor (T x) (R x))
      (-sin (T s) * dT - sin (R s) * dR) s := by
  convert hT.cos.add hR.cos using 1 <;> first | rfl | ring

theorem minkowski_null_boundary (R : ℝ) :
    conformalFactor (π - R) R = 0 ∧ conformalFactor (R - π) R = 0 ∧
    -(sin (π - R))^2 + sin R^2 = 0 ∧ -(sin (R - π))^2 + sin R^2 = 0 := by
  simp [conformalFactor, cos_pi_sub, cos_sub_pi, sin_pi_sub, sin_sub_pi]

theorem minkowski_boundary_regular {R : ℝ} (hR : 0 < R) (hπ : R < π) :
    -sin (π - R) ≠ 0 ∧ -sin (R - π) ≠ 0 := by
  have hs := sin_pos_of_pos_of_lt_pi hR hπ
  simp only [sin_pi_sub, sin_sub_pi, neg_neg]
  exact ⟨neg_ne_zero.mpr hs.ne', hs.ne'⟩

theorem minkowski_three_corners :
    conformalFactor π 0 = 0 ∧ conformalFactor (-π) 0 = 0 ∧ conformalFactor 0 π = 0 ∧
    sin π = 0 ∧ sin (-π) = 0 ∧ sin (0 : ℝ) = 0 := by simp [conformalFactor]

theorem minkowski_corner_derivatives {T R : ℝ → ℝ} {s dT dR : ℝ}
    (hT : HasDerivAt T dT s) (hR : HasDerivAt R dR s)
    (hc : (T s = π ∧ R s = 0) ∨ (T s = -π ∧ R s = 0) ∨
      (T s = 0 ∧ R s = π)) :
    HasDerivAt (fun x => conformalFactor (T x) (R x)) 0 s := by
  have h := conformalFactor_derivative hT hR
  rcases hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simpa [h₁, h₂] using h

theorem minkowski_boundary_derivatives (R : ℝ) :
    HasDerivAt (fun x : ℝ => π - x) (-1) R ∧
    HasDerivAt (fun x : ℝ => x - π) 1 R ∧
    HasDerivAt (fun x => conformalFactor (π - x) x) 0 R ∧
    HasDerivAt (fun x => conformalFactor (x - π) x) 0 R := by
  have hp := (hasDerivAt_id R).const_sub π
  have hm := (hasDerivAt_id R).sub_const π
  refine ⟨by simpa using hp, by simpa using hm, ?_, ?_⟩
  · simpa [sin_pi_sub] using conformalFactor_derivative hp (hasDerivAt_id R)
  · simpa [sin_sub_pi] using conformalFactor_derivative hm (hasDerivAt_id R)

theorem minkowski_corner_limits :
    Tendsto (fun t : ℝ => (minkowskiT t 0, minkowskiR t 0)) atTop (𝓝 (π, 0)) ∧
    Tendsto (fun t : ℝ => (minkowskiT t 0, minkowskiR t 0)) atBot (𝓝 (-π, 0)) ∧
    Tendsto (fun r : ℝ => (minkowskiT 0 r, minkowskiR 0 r)) atTop (𝓝 (0, π)) := by
  have hp := tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop
  have hm := tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot
  refine ⟨?_, ?_, ?_⟩
  · convert (hp.add hp).prodMk_nhds (tendsto_const_nhds (x := (0 : ℝ))) using 1 <;>
      simp [minkowskiT, minkowskiR]
  · convert (hm.add hm).prodMk_nhds (tendsto_const_nhds (x := (0 : ℝ))) using 1 <;>
      simp [minkowskiT, minkowskiR]
    ring
  · convert (tendsto_const_nhds (x := (0 : ℝ))).prodMk_nhds (hp.add hp) using 1 <;>
      simp [minkowskiT, minkowskiR, arctan_neg, sub_eq_add_neg]

/-- Dimensionless global de Sitter time; physical proper time is α times this coordinate. -/
def deSitterEta (t : ℝ) : ℝ := 2 * arctan (exp t) - π / 2
def deSitterTime (η : ℝ) : ℝ := log (tan (η / 2 + π / 4))
def deSitterMetric (α t χ dt dχ dθ dφ θ : ℝ) : ℝ :=
  α^2 * (-dt^2 + cosh t^2 * (dχ^2 + sin χ^2 * angularSpeedSq θ dθ dφ))
def einsteinMetric (χ θ dη dχ dθ dφ : ℝ) : ℝ :=
  -dη^2 + dχ^2 + sin χ^2 * angularSpeedSq θ dθ dφ

theorem deSitterEta_range (t : ℝ) :
    -(π / 2) < deSitterEta t ∧ deSitterEta t < π / 2 := by
  have hp := arctan_pos.mpr (exp_pos t)
  have hu := arctan_lt_pi_div_two (exp t)
  unfold deSitterEta
  constructor <;> linarith

theorem deSitterTime_left_inverse (t : ℝ) : deSitterTime (deSitterEta t) = t := by
  have he : deSitterEta t / 2 + π / 4 = arctan (exp t) := by
    unfold deSitterEta; ring
  rw [deSitterTime, he, tan_arctan, log_exp]

theorem deSitterTime_right_inverse {η : ℝ}
    (hη : -(π / 2) < η) (hπ : η < π / 2) : deSitterEta (deSitterTime η) = η := by
  have h₀ : 0 < η / 2 + π / 4 := by linarith
  have h₁ : η / 2 + π / 4 < π / 2 := by linarith
  rw [deSitterEta, deSitterTime, exp_log (tan_pos_of_pos_of_lt_pi_div_two h₀ h₁),
    arctan_tan (by linarith [Real.pi_pos]) h₁]
  ring

private theorem deSitter_cos_exp (t : ℝ) :
    cos (deSitterEta t) = 2 * exp t / (1 + (exp t)^2) := by
  have hs : sin (arctan (exp t)) = exp t * cos (arctan (exp t)) := by
    exact (div_eq_iff (cos_arctan_pos _).ne').mp (by
      rw [← tan_eq_sin_div_cos, tan_arctan])
  rw [deSitterEta, cos_sub_pi_div_two, sin_two_mul, hs,
    show 2 * (exp t * cos (arctan (exp t))) * cos (arctan (exp t)) =
      2 * exp t * cos (arctan (exp t))^2 by ring, cos_sq_arctan]
  ring

theorem deSitter_cos_cosh (t : ℝ) : cos (deSitterEta t) = 1 / cosh t := by
  rw [deSitter_cos_exp, cosh_eq, exp_neg]
  have he := (exp_pos t).ne'
  have hd : 1 + (exp t)^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

theorem deSitter_cosh_sec (t : ℝ) : cosh t = 1 / cos (deSitterEta t) := by
  rw [deSitter_cos_cosh, one_div_one_div]

theorem deSitterEta_derivative (t : ℝ) :
    HasDerivAt deSitterEta (cos (deSitterEta t)) t := by
  have hd := (((hasDerivAt_exp t).arctan).const_mul 2).sub_const (π / 2)
  rw [deSitter_cos_exp]
  convert hd using 1 <;> first | rfl | ring

theorem deSitterTime_derivative {η : ℝ} (hη : -(π / 2) < η) (hπ : η < π / 2) :
    HasDerivAt deSitterTime (1 / cos η) η := by
  have hx : 0 < η / 2 + π / 4 := by linarith
  have hy : η / 2 + π / 4 < π / 2 := by linarith
  have hc := (cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hy⟩).ne'
  have hs := (sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])).ne'
  have ht := (tan_pos_of_pos_of_lt_pi_div_two hx hy).ne'
  have hu : HasDerivAt (fun x : ℝ => x / 2 + π / 4) (1 / 2) η := by
    simpa only [id_eq] using ((hasDerivAt_id η).div_const 2).add_const (π / 4)
  have hv : HasDerivAt (fun x : ℝ => tan (x / 2 + π / 4))
      (1 / cos (η / 2 + π / 4)^2 * (1 / 2)) η := by
    simpa only [Function.comp_apply] using!
      HasDerivAt.comp (h₂ := Real.tan) (h := fun x : ℝ => x / 2 + π / 4) η
        (Real.hasDerivAt_tan (x := η / 2 + π / 4) hc) hu
  have hd : HasDerivAt (fun x : ℝ => log (tan (x / 2 + π / 4)))
      ((1 / cos (η / 2 + π / 4)^2 * (1 / 2)) / tan (η / 2 + π / 4)) η := hv.log ht
  have he : cos η = 2 * sin (η / 2 + π / 4) * cos (η / 2 + π / 4) := by
    rw [← sin_two_mul, show 2 * (η / 2 + π / 4) = η + π / 2 by ring,
      sin_add_pi_div_two]
  convert hd using 1
  · rfl
  · rw [he, tan_eq_sin_div_cos]
    field_simp

theorem deSitter_weighted_metric_pullback {t χ θ φ : ℝ → ℝ} {s α dt dχ dθ dφ : ℝ}
    (ht : HasDerivAt t dt s) (hχ : HasDerivAt χ dχ s)
    (hθ : HasDerivAt θ dθ s) (hφ : HasDerivAt φ dφ s) :
    cos (deSitterEta (t s))^2 * deSitterMetric α (t s) (χ s) dt dχ dθ dφ (θ s) =
      α^2 * einsteinMetric (χ s) (θ s) (deriv (fun x => deSitterEta (t x)) s)
        (deriv χ s) (deriv θ s) (deriv φ s) := by
  have hη := (deSitterEta_derivative (t s)).comp s ht
  change HasDerivAt (fun x => deSitterEta (t x)) (cos (deSitterEta (t s)) * dt) s at hη
  rw [hη.deriv, hχ.deriv, hθ.deriv, hφ.deriv, deSitter_cos_cosh]
  unfold deSitterMetric einsteinMetric
  have hc := (cosh_pos (t s)).ne'
  field_simp
  ring

def desitterOmega (ℓ η : ℝ) : ℝ := cos η / ℓ

theorem desitter_conformal_metric_pullback {η : ℝ → ℝ} {s dη ℓ : ℝ}
    (hℓ : 0 < ℓ) (hl : -(π / 2) < η s) (hu : η s < π / 2)
    (hη : HasDerivAt η dη s) (v : ℝ) : let τ := fun x => ℓ * deSitterTime (η x);
    -deriv τ s ^ 2 + (ℓ * cosh (τ s / ℓ)) ^ 2 * v ^ 2 =
      (desitterOmega ℓ (η s))⁻¹ ^ 2 * (-dη ^ 2 + v ^ 2) := by
  have hd : HasDerivAt (fun x => ℓ * deSitterTime (η x)) (ℓ * (1 / cos (η s) * dη)) s :=
    ((deSitterTime_derivative hl hu).comp s hη).const_mul ℓ
  have hh := deSitter_cosh_sec (deSitterTime (η s))
  rw [deSitterTime_right_inverse hl hu] at hh
  have hc := (cos_pos_of_mem_Ioo ⟨hl, hu⟩).ne'
  dsimp only
  rw [hd.deriv, mul_div_cancel_left₀ _ hℓ.ne', hh, desitterOmega, inv_div]
  field_simp

theorem deSitter_spacelike_boundary :
    cos (π / 2) = 0 ∧ cos (-(π / 2)) = 0 ∧
    -(sin (π / 2))^2 = -1 ∧ -(sin (-(π / 2)))^2 = -1 ∧
    HasDerivAt cos (-1) (π / 2) ∧ HasDerivAt cos 1 (-(π / 2)) := by
  refine ⟨by simp, by simp, by simp, by simp, ?_, ?_⟩
  · simpa using hasDerivAt_cos (π / 2)
  · simpa using hasDerivAt_cos (-(π / 2))

theorem desitter_scri_spacelike_hypersurface {ℓ : ℝ} (hℓ : 0 < ℓ) (e : Bool) :
    let η := if e then π / 2 else -(π / 2)
    let n := if e then -1 / ℓ else 1 / ℓ
    desitterOmega ℓ η = 0 ∧ HasDerivAt (desitterOmega ℓ) n η ∧ -(n ^ 2) = -1 / ℓ ^ 2 ∧
      -1 / ℓ ^ 2 < 0 := by
  cases e <;> simp [desitterOmega, neg_div, hℓ]
  · simpa only [show desitterOmega ℓ = (fun x => cos x / ℓ) from rfl, one_div] using deSitter_spacelike_boundary.2.2.2.2.2.div_const ℓ
  · simpa only [show desitterOmega ℓ = (fun x => cos x / ℓ) from rfl, neg_div, one_div] using deSitter_spacelike_boundary.2.2.2.2.1.div_const ℓ
theorem deSitter_boundary_induced_positive {χ θ dχ dθ dφ : ℝ}
    (hχ : sin χ ≠ 0) (hθ : sin θ ≠ 0) (hv : dχ ≠ 0 ∨ dθ ≠ 0 ∨ dφ ≠ 0) :
    0 < einsteinMetric χ θ 0 dχ dθ dφ := by
  unfold einsteinMetric angularSpeedSq
  rcases hv with h | h | h <;> positivity

theorem deSitter_boundary_limits :
    Tendsto deSitterEta atTop (𝓝 (π / 2)) ∧
    Tendsto deSitterEta atBot (𝓝 (-(π / 2))) := by
  have hp := (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp tendsto_exp_atTop
  have hm := (continuous_arctan.tendsto 0).comp tendsto_exp_atBot
  constructor
  · convert (hp.const_mul 2).sub_const (π / 2) using 1 <;> first | rfl | ring
  · convert (hm.const_mul 2).sub_const (π / 2) using 1 <;> first | rfl | simp [arctan_zero]

def deSitterScale (α τ : ℝ) : ℝ := α * cosh (τ / α)

theorem deSitterScale_derivative {α : ℝ} (hα : 0 < α) (τ : ℝ) :
    HasDerivAt (deSitterScale α) (sinh (τ / α)) τ := by
  convert (((hasDerivAt_id τ).div_const α).cosh).const_mul α using 1
  · rfl
  · simp only [id_eq]
    field_simp

theorem deSitter_friedmann {α : ℝ} (hα : 0 < α) (τ : ℝ) :
    FLRWCosmologyFriedmann4D.hubble (deSitterScale α) τ = sinh (τ / α) / deSitterScale α τ ∧
    FLRWCosmologyFriedmann4D.hubble (deSitterScale α) τ ^ 2 +
      1 / deSitterScale α τ ^ 2 = 1 / α^2 := by
  have hd := deSitterScale_derivative hα τ
  have hc := (cosh_pos (τ / α)).ne'
  have hH : FLRWCosmologyFriedmann4D.hubble (deSitterScale α) τ =
      sinh (τ / α) / deSitterScale α τ := by
    rw [FLRWCosmologyFriedmann4D.hubble, hd.deriv]
  refine ⟨hH, ?_⟩
  rw [hH, deSitterScale]
  have hs := cosh_sq (τ / α)
  field_simp
  nlinarith only [hs]

theorem deSitter_conformalFactor_pos {η : ℝ} (hη : -(π / 2) < η) (hπ : η < π / 2) :
    0 < cos η := cos_pos_of_mem_Ioo ⟨hη, hπ⟩

theorem causal_angular_displacement {χ θ φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hχ : ∀ s ∈ Icc a b, DifferentiableAt ℝ χ s)
    (hc : ∀ s ∈ Icc a b,
      einsteinMetric (χ s) (θ s) 1 (deriv χ s) (deriv θ s) (deriv φ s) ≤ 0) :
    |χ b - χ a| ≤ b - a := by
  have hb : ∀ s ∈ Icc a b, ‖deriv χ s‖ ≤ (1 : ℝ) := by
    intro s hs
    have h := hc s hs
    have hA : 0 ≤ sin (χ s)^2 * angularSpeedSq (θ s) (deriv θ s) (deriv φ s) := by
      unfold angularSpeedSq; positivity
    have hv : (deriv χ s)^2 ≤ 1 := by unfold einsteinMetric at h; nlinarith
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (deriv χ s + 1), sq_nonneg (deriv χ s - 1)]
  have hm := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le hχ hb
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (sub_nonneg.mpr hab)] using hm

/-- Radial future causal curves use conformal time as parameter. -/
def radialReachable (η₀ χ₀ η₁ χ₁ : ℝ) : Prop :=
  η₀ ≤ η₁ ∧ ∃ γ : ℝ → ℝ, γ η₀ = χ₀ ∧ γ η₁ = χ₁ ∧
    ∀ s ∈ Icc η₀ η₁, ∃ v : ℝ, HasDerivAt γ v s ∧ -1 + v^2 ≤ 0

theorem radialReachable_iff (η₀ χ₀ η₁ χ₁ : ℝ) :
    radialReachable η₀ χ₀ η₁ χ₁ ↔ |χ₁ - χ₀| ≤ η₁ - η₀ := by
  constructor
  · rintro ⟨hη, γ, h₀, h₁, hd⟩
    have hv : ∀ s ∈ Icc η₀ η₁, ‖deriv γ s‖ ≤ (1 : ℝ) := by
      intro s hs
      obtain ⟨v, hdv, hb⟩ := hd s hs
      rw [hdv.deriv, Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [sq_nonneg (v + 1), sq_nonneg (v - 1)]
    have hm := (convex_Icc η₀ η₁).norm_image_sub_le_of_norm_deriv_le
      (fun s hs => (hd s hs).choose_spec.1.differentiableAt) hv
      (left_mem_Icc.mpr hη) (right_mem_Icc.mpr hη)
    simpa only [h₀, h₁, Real.norm_eq_abs, one_mul, abs_of_nonneg (sub_nonneg.mpr hη)] using hm
  · intro h
    have hη : η₀ ≤ η₁ := by linarith [abs_nonneg (χ₁ - χ₀)]
    refine ⟨hη, ?_⟩
    by_cases he : η₁ = η₀
    · have hx : χ₁ = χ₀ := by
        have hz : |χ₁ - χ₀| = 0 := by linarith [abs_nonneg (χ₁ - χ₀)]
        exact sub_eq_zero.mp (abs_eq_zero.mp hz)
      refine ⟨fun _ => χ₀, rfl, hx.symm, ?_⟩
      intro s hs
      exact ⟨0, hasDerivAt_const s χ₀, by norm_num⟩
    · have hp : 0 < η₁ - η₀ := sub_pos.mpr (lt_of_le_of_ne hη (Ne.symm he))
      let v := (χ₁ - χ₀) / (η₁ - η₀)
      have hv : |v| ≤ 1 := by
        dsimp [v]
        rw [abs_div, abs_of_pos hp, div_le_one hp]
        exact h
      refine ⟨fun s => χ₀ + v * (s - η₀), by ring, ?_, ?_⟩
      · dsimp [v]; field_simp; ring
      · intro s hs
        refine ⟨v, ?_, ?_⟩
        · convert (((hasDerivAt_id s).sub_const η₀).const_mul v).const_add χ₀ using 1 <;> simp
        · have hv' := abs_le.mp hv
          nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - v) (by linarith : 0 ≤ 1 + v)]

/-- Causal spherical coordinate curves, with conformal time as parameter. -/
def sphericalReachable (η₀ χ₀ η₁ χ₁ : ℝ) : Prop :=
  η₀ ≤ η₁ ∧ ∃ χ θ φ : ℝ → ℝ, χ η₀ = χ₀ ∧ χ η₁ = χ₁ ∧
    (∀ s ∈ Icc η₀ η₁, DifferentiableAt ℝ χ s ∧
      DifferentiableAt ℝ θ s ∧ DifferentiableAt ℝ φ s) ∧
    ∀ s ∈ Icc η₀ η₁,
      einsteinMetric (χ s) (θ s) 1 (deriv χ s) (deriv θ s) (deriv φ s) ≤ 0

theorem sphericalReachable_iff (η₀ χ₀ η₁ χ₁ : ℝ) :
    sphericalReachable η₀ χ₀ η₁ χ₁ ↔ |χ₁ - χ₀| ≤ η₁ - η₀ := by
  constructor
  · rintro ⟨hη, χ, θ, φ, h₀, h₁, hd, hc⟩
    simpa only [h₀, h₁] using causal_angular_displacement hη (fun s hs => (hd s hs).1) hc
  · intro h
    obtain ⟨hη, γ, h₀, h₁, hd⟩ := (radialReachable_iff η₀ χ₀ η₁ χ₁).mpr h
    refine ⟨hη, γ, (fun _ => 0), (fun _ => 0), h₀, h₁, ?_, ?_⟩
    · intro s hs
      exact ⟨(hd s hs).choose_spec.1.differentiableAt,
        differentiableAt_const 0, differentiableAt_const 0⟩
    · intro s hs
      obtain ⟨v, hv, hc⟩ := hd s hs
      simpa [einsteinMetric, angularSpeedSq, hv.deriv] using hc

theorem deSitter_causal_diamond {ηlo ηhi η χ : ℝ} (hχ : 0 ≤ χ) :
    (sphericalReachable ηlo 0 η χ ∧ sphericalReachable η χ ηhi 0) ↔
      χ ≤ min (η - ηlo) (ηhi - η) := by
  rw [sphericalReachable_iff, sphericalReachable_iff, sub_zero, zero_sub, abs_neg,
    abs_of_nonneg hχ, le_min_iff]

theorem desitter_causal_horizon_dichotomy {η χ : ℝ} (hχ : 0 ≤ χ) :
    (∃ lo hi, -(π / 2) < lo ∧ hi < π / 2 ∧
      sphericalReachable lo 0 η χ ∧ sphericalReachable η χ hi 0) ↔ |η| + χ < π / 2 := by
  rw [← lt_sub_iff_add_lt, abs_lt]
  constructor
  · rintro ⟨lo, hi, hlo, hhi, h⟩
    obtain ⟨ha, hb⟩ := le_min_iff.mp ((deSitter_causal_diamond hχ).mp h)
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨ha, hb⟩
    refine ⟨(-(π / 2) + η - χ) / 2, (π / 2 + η + χ) / 2, by linarith, by linarith,
      (deSitter_causal_diamond hχ).mpr (le_min ?_ ?_)⟩ <;> linarith

open OmegaMath.ExponentialRadialCoordinates in
abbrev kruskalF := profile
abbrev U_ext := OmegaMath.ExponentialRadialCoordinates.leftCoordinate
abbrev V_ext := OmegaMath.ExponentialRadialCoordinates.rightCoordinate
abbrev kruskalFactor := OmegaMath.ExponentialRadialCoordinates.coefficient
abbrev cycloidRadius := OmegaMath.ExponentialRadialCoordinates.cycloidalRadius
abbrev cycloidTime := OmegaMath.ExponentialRadialCoordinates.cycloidalTime

abbrev rStar := OmegaMath.ExponentialRadialCoordinates.logarithmicRadius

open OmegaMath.ExponentialRadialCoordinates in
theorem kruskalF_deriv_and_strict_anti {M : ℝ} (hM : 0 < M) :
    (∀ r, HasDerivAt (kruskalF M) (-r / (4 * M ^ 2) * Real.exp (r / (2 * M))) r) ∧
    StrictAntiOn (kruskalF M) (Set.Ici 0) ∧ kruskalF M 0 = 1 ∧ kruskalF M (2 * M) = 0 ∧
    (∀ r ∈ Set.Ioo 0 (2 * M), kruskalF M r ∈ Set.Ioo 0 1) ∧
    (∀ r > 2 * M, kruskalF M r < 0) ∧
    Filter.Tendsto (kruskalF M) Filter.atTop Filter.atBot ∧
    Set.BijOn (kruskalF M) (Set.Ioi 0) (Set.Iio 1) := by
  refine ⟨hasDerivAt_profile hM.ne', strictAntiOn_profile hM, profile_zero M,
    profile_boundary hM.ne', ?_, ?_, tendsto_profile hM, bijOn_profile hM⟩
  · exact fun r hr => ⟨(profile_sign hM).1.2 hr.2, profile_lt_one hM hr.1⟩
  · exact fun _ hr => (profile_sign hM).2.2.2 hr

open OmegaMath.ExponentialRadialCoordinates in
theorem kruskal_uv_product_and_ratio {M r : ℝ} (hM : 0 < M) (hr : 2 * M < r) (t : ℝ) :
    U_ext M t r < 0 ∧ 0 < V_ext M t r ∧ U_ext M t r * V_ext M t r = kruskalF M r ∧
    V_ext M t r / (-U_ext M t r) = Real.exp (t / (2 * M)) ∧
    2 * M * Real.log (V_ext M t r / (-U_ext M t r)) = t ∧
    U_ext M t r = -Real.exp ((rStar M r - t) / (4 * M)) ∧
    V_ext M t r = Real.exp ((rStar M r + t) / (4 * M)) := by
  obtain ⟨hu, hv⟩ := exterior_signs hM hr t
  have hratio := exterior_ratio hM hr t
  refine ⟨hu, hv, exterior_product hM hr.le t, hratio, ?_,
    exterior_exponential_coordinates hM hr t⟩
  rw [hratio, Real.log_exp]
  field_simp

theorem kruskal_metric_analytic_pullback {M s dt dr : ℝ} {t r : ℝ → ℝ}
    (hM : 0 < M) (hR : 2 * M < r s) (ht : HasDerivAt t dt s) (hr : HasDerivAt r dr s)
    (a : ℝ) :
    -(1 - 2 * M / r s) * dt ^ 2 + (1 - 2 * M / r s)⁻¹ * dr ^ 2 + (r s) ^ 2 * a ^ 2 =
      -kruskalFactor M (r s) * deriv (fun x => U_ext M (t x) (r x)) s *
        deriv (fun x => V_ext M (t x) (r x)) s + (r s) ^ 2 * a ^ 2 := by
  rw [OmegaMath.ExponentialRadialCoordinates.exterior_curve_identity hM hR ht hr]

open OmegaMath.ExponentialRadialCoordinates in
theorem kruskal_horizon_nonsingular {M : ℝ} (hM : 0 < M) :
    (∀ r > 0, 0 < kruskalFactor M r) ∧
    kruskalFactor M (2 * M) = 16 * M ^ 2 * Real.exp (-1) ∧
    BlackHoleThermodynamics4D.rPlus M 0 0 = 2 * M ∧
    (∀ q < 1, ∃ g : ℝ → ℝ, 0 < g q ∧ AnalyticAt ℝ g q ∧
      (∀ᶠ w in nhds q, kruskalF M (g w) = w) ∧
      AnalyticAt ℝ (fun w => kruskalFactor M (g w)) q) := by
  refine ⟨fun _ hr => coefficient_pos hM hr, coefficient_boundary hM.ne', ?_, ?_⟩
  · simp [BlackHoleThermodynamics4D.rPlus, BlackHoleThermodynamics4D.horizonGap,
      BlackHoleThermodynamics4D.spin, Real.sqrt_sq hM.le]
    ring
  · intro q hq
    obtain ⟨r, ⟨hr, hqr⟩, _⟩ := existsUnique_radius hM hq
    rw [← hqr]
    obtain ⟨g, hg, hl, hright, _⟩ := exists_analytic_inverse hM.ne' hr.ne'
    have hgr : g (kruskalF M r) = r := Filter.EventuallyEq.eq_of_nhds hl
    refine ⟨g, hgr.symm ▸ hr, hg, hright, ?_⟩
    change AnalyticAt ℝ (fun w => (32 * M ^ 3 / g w) *
      Real.exp (-g w / (2 * M))) (kruskalF M r)
    exact (analyticAt_const.div hg (hgr.symm ▸ hr.ne')).mul
      (by fun_prop)

open OmegaMath.ExponentialRadialCoordinates in
theorem kruskal_regionII_trapping_no_escape {M s dr du dv : ℝ} {r u v : ℝ → ℝ}
    (hM : 0 < M) (hr : 0 < r s) (hu0 : 0 < u s) (hv0 : 0 < v s)
    (hdu : 0 ≤ du) (hdv : 0 ≤ dv) (hsum : 0 < du + dv) (hd : HasDerivAt r dr s)
    (hu : HasDerivAt u du s) (hv : HasDerivAt v dv s)
    (he : ∀ᶠ x in nhds s, u x * v x = kruskalF M (r x)) :
    HasDerivAt (fun x => u x * v x) (du * v s + u s * dv) s ∧
      0 < du * v s + u s * dv ∧ dr < 0 ∧ r s < 2 * M := by
  have hp : 0 < du * v s + u s * dv := by
    rcases lt_or_eq_of_le hdu with hp | hz
    · exact add_pos_of_pos_of_nonneg (mul_pos hp hv0) (mul_nonneg hu0.le hdv)
    · have hv' : 0 < dv := by linarith
      exact add_pos_of_nonneg_of_pos (mul_nonneg hdu hv0.le) (mul_pos hu0 hv')
  refine ⟨hu.mul hv, hp, ?_, (profile_sign hM).1.1 ?_⟩
  · rw [radius_derivative_of_equation hM.ne' hr hd hu hv (he.mono fun _ h => h.symm)]
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
      (neg_neg_of_pos (by positivity)) (Real.exp_pos _)) hp
  · change 0 < kruskalF M (r s)
    rw [← Filter.EventuallyEq.eq_of_nhds he]
    exact mul_pos hu0 hv0

theorem kruskal_singularity_spacelike {T X : ℝ → ℝ} {s dT dX : ℝ}
    (hT : HasDerivAt T dT s) (hX : HasDerivAt X dX s) (hn : dX ≠ 0)
    (he : ∀ᶠ x in nhds s, (T x) ^ 2 - (X x) ^ 2 = 1) :
    -(dT ^ 2) + dX ^ 2 = dX ^ 2 / (T s) ^ 2 ∧ 0 < -(dT ^ 2) + dX ^ 2 := by
  have hh := ((hT.pow 2).sub (hX.pow 2)).congr_of_eventuallyEq (he.mono fun _ h => h.symm)
  have hz := hh.unique (hasDerivAt_const s (1 : ℝ))
  norm_num at hz
  have hv : (T s) ^ 2 - (X s) ^ 2 = 1 := Filter.EventuallyEq.eq_of_nhds he
  have hT0 : T s ≠ 0 := by
    intro h
    rw [h] at hv
    nlinarith [sq_nonneg (X s)]
  have hid : -(dT ^ 2) + dX ^ 2 = dX ^ 2 / (T s) ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hT0)).2
    have hlin : T s * dT - X s * dX = 0 := by nlinarith only [hz]
    linear_combination dX ^ 2 * hv - (T s * dT + X s * dX) * hlin
  exact ⟨hid, hid.symm ▸ div_pos (sq_pos_of_ne_zero hn) (sq_pos_of_ne_zero hT0)⟩

theorem einstein_rosen_bridge_minimal_throat {M r U V : ℝ} (hM : 0 < M)
    (hT : (V + U) / 2 = 0) (he : U * V = kruskalF M r) :
    2 * M ≤ r ∧ (r = 2 * M ↔ (V - U) / 2 = 0) := by
  apply OmegaMath.ExponentialRadialCoordinates.radius_minimum hM
  change kruskalF M r = _
  rw [← he]
  nlinarith only [congrArg (fun x : ℝ => x * (V + U)) hT]

open OmegaMath.ExponentialRadialCoordinates in
theorem schwarzschild_interior_proper_time_bound {M : ℝ} (hM : 0 < M) :
    (∀ η, HasDerivAt (cycloidRadius M) (-M * Real.sin η) η ∧
      HasDerivAt (cycloidTime M) (cycloidRadius M η) η) ∧
    (∀ η ∈ Set.Ioo 0 Real.pi,
      ((-M * Real.sin η) / cycloidRadius M η) ^ 2 = 2 * M / cycloidRadius M η - 1) ∧
    cycloidTime M Real.pi - cycloidTime M 0 = Real.pi * M ∧
    (∀ (τ dτ : ℝ → ℝ), ContinuousOn τ (Set.Icc 0 Real.pi) →
      (∀ η ∈ Set.Ioo 0 Real.pi, HasDerivAt τ (dτ η) η) →
      (∀ η ∈ Set.Ioo 0 Real.pi,
        dτ η ^ 2 * (2 * M / cycloidRadius M η - 1) ≤ (-M * Real.sin η) ^ 2) →
      τ Real.pi - τ 0 ≤ Real.pi * M) := by
  refine ⟨fun η => ⟨hasDerivAt_cycloidalRadius M η, hasDerivAt_cycloidalTime M η⟩,
    (fun _ hη => cycloidal_squared_ratio hM hη), ?_, ?_⟩
  · obtain ⟨_, _, h0, hπ⟩ := cycloidal_endpoints M
    simp [h0, hπ]
  · intro τ dτ hτ hd hw
    apply cycloidal_time_bound hτ hd
    intro η hη
    have hr := cycloidal_interior hM hη
    have hp : 0 < 2 * M / cycloidRadius M η - 1 := sub_pos.mpr ((one_lt_div hr.1).2 hr.2)
    have he := cycloidal_squared_ratio hM hη
    rw [div_pow] at he
    have he' := (div_eq_iff (pow_ne_zero 2 hr.1.ne')).mp he
    have hs : dτ η ^ 2 ≤ cycloidRadius M η ^ 2 := by
      apply le_of_mul_le_mul_right _ hp
      calc
        _ ≤ (-M * Real.sin η) ^ 2 := hw η hη
        _ = _ := he'.trans (mul_comm _ _)
    nlinarith only [hs, hr.1]

theorem schwarzschild_inverse_proper_time_derivative {M r dr : ℝ}
    (hr : 0 < r) (hi : r < 2 * M)
    (hd : 2 * M / r - 1 ≤ dr ^ 2) :
    |dr⁻¹| ≤ 1 / Real.sqrt (2 * M / r - 1) := by
  have hp : 0 < 2 * M / r - 1 := sub_pos.mpr ((one_lt_div hr).2 hi)
  have hs : Real.sqrt (2 * M / r - 1) ≤ |dr| := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hd
  rw [abs_inv, one_div]
  exact inv_anti₀ (Real.sqrt_pos.2 hp) hs

end D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
