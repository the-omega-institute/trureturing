/- GID: D5/S3/Quantum/PositiveResolvent/EulerResolvent
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real Euler resolvent integrals and elementary logarithmic density kernels. -/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.MeasureTheory.Function.JacobianOneDim

noncomputable section
open Real Set MeasureTheory intervalIntegral
open scoped Real

namespace D5.S3.Quantum.PositiveResolvent.EulerResolvent

def E (s u : ℝ) : ℝ := 1 / (Real.log (u / s) ^ 2 + Real.pi ^ 2)
def H (s u : ℝ) : ℝ := (s + u) * E s u
def k (s t : ℝ) : ℝ := 1 / Real.pi ^ 2 *
  ∫ θ in (0:ℝ)..1, Real.sin (Real.pi * θ) ^ 2 * s ^ (1 - θ) * t ^ θ

private lemma exp_sin_primitive (v a q : ℝ) (hd : v ^ 2 + a ^ 2 ≠ 0) :
    HasDerivAt (fun θ => Real.exp (v * θ) *
      (v * Real.sin (a * θ) - a * Real.cos (a * θ)) / (v ^ 2 + a ^ 2))
      (Real.exp (v * q) * Real.sin (a * q)) q := by
  have h := (((Real.hasDerivAt_exp (v * q)).comp q
    ((hasDerivAt_id q).const_mul v)).mul
    ((((Real.hasDerivAt_sin (a * q)).comp q
      ((hasDerivAt_id q).const_mul a)).const_mul v).sub
      (((Real.hasDerivAt_cos (a * q)).comp q
        ((hasDerivAt_id q).const_mul a)).const_mul a))).div_const (v ^ 2 + a ^ 2)
  convert h using 1 <;> (first | rfl | (dsimp; field_simp [hd]; ring))

private lemma exp_cos_primitive (v a q : ℝ) (hd : v ^ 2 + a ^ 2 ≠ 0) :
    HasDerivAt (fun θ => Real.exp (v * θ) *
      (v * Real.cos (a * θ) + a * Real.sin (a * θ)) / (v ^ 2 + a ^ 2))
      (Real.exp (v * q) * Real.cos (a * q)) q := by
  have h := (((Real.hasDerivAt_exp (v * q)).comp q
    ((hasDerivAt_id q).const_mul v)).mul
    ((((Real.hasDerivAt_cos (a * q)).comp q
      ((hasDerivAt_id q).const_mul a)).const_mul v).add
      (((Real.hasDerivAt_sin (a * q)).comp q
        ((hasDerivAt_id q).const_mul a)).const_mul a))).div_const (v ^ 2 + a ^ 2)
  convert h using 1 <;> (first | rfl | (dsimp; field_simp [hd]; ring))

/-- Exponential-sine integral, including the zero exponential parameter. -/
theorem integral_exp_sin (v : ℝ) :
    (∫ θ in (0:ℝ)..1, Real.exp (v * θ) * Real.sin (Real.pi * θ)) =
      Real.pi * (Real.exp v + 1) / (v ^ 2 + Real.pi ^ 2) := by
  have hd : v ^ 2 + Real.pi ^ 2 ≠ 0 := by positivity
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => exp_sin_primitive v Real.pi θ hd)
    (show IntervalIntegrable (fun θ => Real.exp (v * θ) * Real.sin (Real.pi * θ))
      volume 0 1 from (by fun_prop : Continuous _).intervalIntegrable 0 1)
  simp only [mul_one, mul_zero, Real.exp_zero, Real.sin_zero, Real.cos_zero,
    Real.sin_pi, Real.cos_pi] at h
  rw [h]
  ring

private lemma integral_exp_cos_two_pi (v : ℝ) :
    (∫ θ in (0:ℝ)..1, Real.exp (v * θ) * Real.cos (2 * Real.pi * θ)) =
      v * (Real.exp v - 1) / (v ^ 2 + 4 * Real.pi ^ 2) := by
  have hd : v ^ 2 + (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => exp_cos_primitive v (2 * Real.pi) θ hd)
    (show IntervalIntegrable (fun θ => Real.exp (v * θ) * Real.cos (2 * Real.pi * θ))
      volume 0 1 from (by fun_prop : Continuous _).intervalIntegrable 0 1)
  simp only [mul_one, mul_zero, Real.exp_zero, Real.sin_zero, Real.cos_zero,
    Real.sin_two_pi, Real.cos_two_pi] at h
  rw [h]
  ring

/-- The sine-square integral away from the zero exponential parameter. -/
theorem integral_exp_sin_sq (v : ℝ) (hv : v ≠ 0) :
    (∫ θ in (0:ℝ)..1, Real.exp (v * θ) * Real.sin (Real.pi * θ) ^ 2) =
      2 * Real.pi ^ 2 * (Real.exp v - 1) / (v * (v ^ 2 + 4 * Real.pi ^ 2)) := by
  have hi : IntervalIntegrable (fun θ => Real.exp (v * θ)) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable 0 1
  have hic : IntervalIntegrable (fun θ => Real.exp (v * θ) * Real.cos (2 * Real.pi * θ))
    volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable 0 1
  have hs : (fun θ : ℝ => Real.exp (v * θ) * Real.sin (Real.pi * θ)^2) =
      fun θ => (Real.exp (v * θ) - Real.exp (v * θ) * Real.cos (2 * Real.pi * θ)) / 2 := by
    funext θ
    rw [show 2 * Real.pi * θ = 2 * (Real.pi * θ) by ring, Real.cos_two_mul]
    rw [Real.sin_sq]
    ring
  rw [hs, intervalIntegral.integral_div, intervalIntegral.integral_sub hi hic,
    integral_exp_cos_two_pi]
  have he : (∫ θ in (0:ℝ)..1, Real.exp (v * θ)) = (Real.exp v - 1) / v := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ _ => (((Real.hasDerivAt_exp (v * θ)).comp θ
        ((hasDerivAt_id θ).const_mul v)).div_const v).congr_deriv
        (by field_simp)) hi
    simp only [Function.comp_apply, mul_one, mul_zero, Real.exp_zero] at hh
    rw [hh]
    ring
  rw [he]
  field_simp
  ring

/-- Zero exponential parameter in the sine-square integral. -/
theorem integral_sin_sq_pi :
    (∫ θ in (0:ℝ)..1, Real.sin (Real.pi * θ)^2) = 1 / 2 := by
  have h := intervalIntegral.integral_comp_mul_left
    (fun θ : ℝ => Real.sin θ ^ 2) Real.pi_ne_zero (a := 0) (b := 1)
  rw [integral_sin_sq] at h
  simp only [mul_one, mul_zero, Real.sin_zero, Real.cos_zero, Real.sin_pi, Real.cos_pi] at h
  rw [h]
  simp only [smul_eq_mul]
  field_simp
  ring

private lemma powers_as_exp (s u θ : ℝ) (hs : 0 < s) (hu : 0 < u) :
    s ^ (1 - θ) * u ^ θ = s * Real.exp (Real.log (u / s) * θ) := by
  rw [Real.rpow_def_of_pos hs, Real.rpow_def_of_pos hu,
    Real.log_div hu.ne' hs.ne', ← Real.exp_add,
    show Real.log s * (1 - θ) + Real.log u * θ =
      Real.log s + (Real.log u - Real.log s) * θ by ring,
    Real.exp_add, Real.exp_log hs]

/-- Formula (3), valid also when its positive parameters coincide. -/
theorem H_eq_integral (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    H s u = 1 / Real.pi *
      ∫ θ in (0:ℝ)..1, Real.sin (Real.pi * θ) * s ^ (1 - θ) * u ^ θ := by
  have heq : (fun θ : ℝ => Real.sin (Real.pi * θ) * s ^ (1 - θ) * u ^ θ) =
      fun θ => s * (Real.exp (Real.log (u / s) * θ) * Real.sin (Real.pi * θ)) := by
    funext θ
    rw [mul_assoc, powers_as_exp s u θ hs hu]
    ring
  rw [heq, intervalIntegral.integral_const_mul, integral_exp_sin,
    Real.exp_log (div_pos hu hs)]
  unfold H E
  field_simp
  ring

/-- Formula (4) away from the diagonal. -/
theorem k_eq_closed (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (hst : t ≠ s) :
    k s t = 2 * (t - s) /
      (Real.log (t / s) * (Real.log (t / s)^2 + 4 * Real.pi^2)) := by
  have hl : Real.log (t / s) ≠ 0 := by
    intro h
    have := Real.log_eq_zero.mp h
    rcases this with h | h | h
    · exact (div_pos ht hs).ne' h
    · exact hst ((div_eq_one_iff_eq hs.ne').mp h)
    · linarith [div_pos ht hs]
  unfold k
  have heq : (fun θ : ℝ => Real.sin (Real.pi * θ)^2 * s ^ (1 - θ) * t ^ θ) =
      fun θ => s * (Real.exp (Real.log (t / s) * θ) * Real.sin (Real.pi * θ)^2) := by
    funext θ
    rw [mul_assoc, powers_as_exp s t θ hs ht]
    ring
  rw [heq, intervalIntegral.integral_const_mul, integral_exp_sin_sq _ hl,
    Real.exp_log (div_pos ht hs)]
  field_simp

/-- The continuous diagonal value in formula (4). -/
theorem k_diag (s : ℝ) (hs : 0 < s) : k s s = s / (2 * Real.pi ^ 2) := by
  unfold k
  have heq : (fun θ : ℝ => Real.sin (Real.pi * θ)^2 * s ^ (1 - θ) * s ^ θ) =
      fun θ => s * Real.sin (Real.pi * θ)^2 := by
    funext θ
    rw [mul_assoc, powers_as_exp s s θ hs hs]
    simp
    ring
  rw [heq, intervalIntegral.integral_const_mul, integral_sin_sq_pi]
  ring

private lemma euler_substitution_image :
    (fun q : ℝ => q / (1 - q)) '' Ioo 0 1 = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact div_pos hq.1 (by linarith [hq.2])
  · intro ht
    have ht : 0 < t := ht
    refine ⟨t / (1 + t), ⟨div_pos ht (by positivity), ?_⟩, ?_⟩
    · exact (div_lt_one (by positivity : 0 < 1 + t)).mpr (by linarith)
    · field_simp
      ring

private lemma euler_substitution_deriv (q : ℝ) (hq : q ∈ Ioo 0 1) :
    HasDerivAt (fun q : ℝ => q / (1 - q)) (1 / (1 - q)^2) q := by
  have h := (hasDerivAt_id q).div ((hasDerivAt_const q 1).sub (hasDerivAt_id q))
    (by linarith [hq.2] : 1 - q ≠ 0)
  convert h using 1 <;> (first | rfl | (dsimp; congr 1; ring))

private lemma euler_substitution_injective :
    InjOn (fun q : ℝ => q / (1 - q)) (Ioo 0 1) := by
  intro q hq r hr h
  have hq0 : 1 - q ≠ 0 := by linarith [hq.2]
  have hr0 : 1 - r ≠ 0 := by linarith [hr.2]
  have := (div_eq_div_iff hq0 hr0).mp h
  nlinarith

private lemma euler_substitution_integrand (θ q : ℝ) (hq : q ∈ Ioo 0 1) :
    |1 / (1 - q)^2| * ((q / (1 - q)) ^ (-θ) / (1 + q / (1 - q))) =
      q ^ (-θ) * (1 - q) ^ (θ - 1) := by
  have hp : 0 < 1 - q := by linarith [hq.2]
  have hden : 1 + q / (1 - q) = 1 / (1 - q) := by field_simp; ring
  rw [abs_of_pos (by positivity : 0 < 1 / (1 - q)^2), hden,
    Real.div_rpow hq.1.le hp.le, Real.rpow_neg hp.le,
    Real.rpow_sub_one hp.ne']
  field_simp

private lemma euler_unit_integral (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∫ t in Ioi (0:ℝ), t ^ (-θ) / (1 + t)) = Real.pi / Real.sin (Real.pi * θ) := by
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun q hq => (euler_substitution_deriv q hq).hasDerivWithinAt)
    euler_substitution_injective (fun t : ℝ => t ^ (-θ) / (1 + t))
  rw [euler_substitution_image] at hj
  have hid : (∫ t in Ioi (0:ℝ), t ^ (-θ) / (1 + t)) =
      ∫ q in (0:ℝ)..1, q ^ (-θ) * (1 - q) ^ (θ - 1) := by
    rw [hj, intervalIntegral.integral_of_le zero_le_one,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro q hq
    exact euler_substitution_integrand θ q hq
  have hb : Complex.betaIntegral (1 - (θ:ℂ)) θ =
      ((∫ q in (0:ℝ)..1, q ^ (-θ) * (1 - q) ^ (θ - 1) : ℝ) : ℂ) := by
    unfold Complex.betaIntegral
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro q hq
    rw [uIcc_of_le zero_le_one] at hq
    have h1 : (1 - (θ:ℂ)) - 1 = ((-θ:ℝ):ℂ) := by push_cast; ring
    have h2 : (θ:ℂ) - 1 = ((θ - 1:ℝ):ℂ) := by push_cast; rfl
    change (q:ℂ)^((1-(θ:ℂ))-1) * (1-(q:ℂ))^((θ:ℂ)-1) =
      ((q^(-θ) * (1-q)^(θ-1):ℝ):ℂ)
    rw [h1, h2, show (1:ℂ) - (q:ℂ) = ((1-q:ℝ):ℂ) by push_cast; rfl, ← Complex.ofReal_cpow hq.1,
      ← Complex.ofReal_cpow (by linarith [hq.2] : 0 ≤ 1 - q), ← Complex.ofReal_mul]
  have heval := Complex.betaIntegral_eq_Gamma_mul_div (1 - (θ:ℂ)) θ
    (by simp; linarith) (by simpa using hθ0)
  rw [show (1 - (θ:ℂ)) + θ = 1 by ring, Complex.Gamma_one, div_one,
    mul_comm, Complex.Gamma_mul_Gamma_one_sub] at heval
  rw [hb] at heval
  have hs : Real.sin (Real.pi * θ) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])).ne'
  rw [hid]
  apply Complex.ofReal_injective
  convert heval using 1 <;> push_cast <;> rfl

/-- Absolute convergence of the Euler resolvent integral in formula (1). -/
theorem euler_resolvent_integrable (θ u : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hu : 0 < u) : IntegrableOn (fun t => t ^ (-θ) / (u + t)) (Ioi 0) := by
  have hp : 1 - θ ∈ Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hi : IntegrableOn (fun t => Real.rpowIntegrand₀₁ (1-θ) t u / u) (Ioi 0) :=
    (Real.integrableOn_rpowIntegrand₀₁_Ioi hp hu.le).div_const u
  apply hi.congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp
  rw [Real.rpowIntegrand₀₁_eq_pow_div hp ht.le hu.le]
  have he : 1 - θ - 1 = -θ := by ring
  rw [he]
  field_simp
  rw [add_comm]

/-- Euler's real resolvent formula (1). -/
theorem euler_resolvent (θ u : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : 0 < u) :
    u ^ (-θ) = Real.sin (Real.pi * θ) / Real.pi *
      ∫ t in Ioi (0:ℝ), t ^ (-θ) / (u + t) := by
  have hscale := integral_comp_mul_left_Ioi'
    (fun t : ℝ => t ^ (-θ) / (u + t)) 0 hu
  simp only [mul_zero, smul_eq_mul] at hscale
  have hid : (∫ t in Ioi (0:ℝ), (u * t) ^ (-θ) / (u + u * t)) =
      (u ^ (-θ) / u) * (∫ t in Ioi (0:ℝ), t ^ (-θ) / (1 + t)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp
    rw [Real.mul_rpow hu.le ht.le]
    field_simp
  rw [hid, euler_unit_integral θ hθ0 hθ1] at hscale
  rw [← hscale]
  have hs : Real.sin (Real.pi * θ) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])).ne'
  field_simp [hs, hu.ne', Real.pi_ne_zero]
  simp only [mul_comm θ Real.pi, mul_inv_cancel₀ hs, div_self hs]

/-- Symmetry of the integral kernel, including its diagonal. -/
theorem k_symm (s t : ℝ) : k s t = k t s := by
  unfold k
  congr 1
  have h := intervalIntegral.integral_comp_mul_add
    (fun θ : ℝ => Real.sin (Real.pi * θ)^2 * s^(1-θ) * t^θ)
    (a := 0) (b := 1) (c := -1) (by norm_num) 1
  simp only [mul_zero, mul_one, zero_add, neg_add_cancel, inv_neg, inv_one,
    neg_smul, one_smul] at h
  rw [intervalIntegral.integral_symm (a := 0) (b := 1)] at h
  have h2 : (∫ θ in (0:ℝ)..1, Real.sin (Real.pi * (-1*θ+1))^2 *
      s^(1-(-1*θ+1)) * t^(-1*θ+1)) =
      ∫ θ in (0:ℝ)..1, Real.sin (Real.pi*θ)^2 * s^(1-θ) * t^θ := by
    simpa only [neg_neg] using h
  rw [← h2]
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp
  have hs : Real.pi * (-1 * θ + 1) = Real.pi - Real.pi * θ := by ring
  rw [hs, Real.sin_pi_sub]
  have hpow : 1 - (-1 * θ + 1) = θ := by ring
  rw [hpow, show -1 * θ + 1 = 1 - θ by ring]
  ring

/-- Strict positivity of the positive double-resolvent kernel. -/
theorem k_pos (s t : ℝ) (hs : 0 < s) (ht : 0 < t) : 0 < k s t := by
  by_cases hst : s = t
  · subst t
    rw [k_diag s hs]
    positivity
  unfold k
  apply mul_pos (by positivity)
  apply intervalIntegral.integral_pos zero_lt_one
  · apply Continuous.continuousOn
    fun_prop (disch := positivity)
  · intro θ hθ
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos hs _).le)
      (Real.rpow_pos_of_pos ht _).le
  · refine ⟨1/2, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [show Real.pi * (1/2:ℝ) = Real.pi/2 by ring, Real.sin_pi_div_two]
    positivity

/-- Absolute convergence of the divided-power resolvent, including equal nodes. -/
theorem power_divdiff_integrable (θ u v : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hu : 0 < u) (hv : 0 < v) :
    IntegrableOn (fun t => t ^ θ / ((u+t)*(v+t))) (Ioi 0) := by
  have hi := euler_resolvent_integrable (1-θ) u (by linarith) (by linarith) hu
  refine hi.mono' ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply continuousOn_of_forall_continuousAt
    intro t ht
    have ht : 0 < t := ht
    fun_prop (disch := positivity)
  · apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    have ht : 0 < t := ht
    rw [Real.norm_of_nonneg (by positivity), show -(1-θ) = θ-1 by ring,
      Real.rpow_sub_one ht.ne']
    rw [div_div]
    have hden : t*(u+t) ≤ (u+t)*(v+t) := by
      nlinarith [mul_pos (add_pos hu ht) hv]
    exact div_le_div_of_nonneg_left (Real.rpow_pos_of_pos ht θ).le (by positivity) hden

/-- Formula (2) at distinct positive nodes; its diagonal is interpreted by a derivative. -/
theorem power_divdiff_resolvent (θ u v : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v) :
    (u ^ θ - v ^ θ) / (u - v) = Real.sin (Real.pi * θ) / Real.pi *
      ∫ t in Ioi (0:ℝ), t ^ θ / ((u+t)*(v+t)) := by
  have hiu := (euler_resolvent_integrable (1-θ) u (by linarith) (by linarith) hu).const_mul u
  have hiv := (euler_resolvent_integrable (1-θ) v (by linarith) (by linarith) hv).const_mul v
  have heq : (∫ t in Ioi (0:ℝ), t ^ θ / ((u+t)*(v+t))) =
      (u * (∫ t in Ioi (0:ℝ), t ^ (-(1-θ)) / (u+t)) -
       v * (∫ t in Ioi (0:ℝ), t ^ (-(1-θ)) / (v+t))) / (u-v) := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_sub hiu hiv, ← MeasureTheory.integral_div]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht : 0<t := ht
    dsimp
    rw [show -(1-θ) = θ-1 by ring, Real.rpow_sub_one ht.ne']
    field_simp [ht.ne', (add_pos hu ht).ne', (add_pos hv ht).ne', sub_ne_zero.mpr huv]
    <;> ring
  have heu := euler_resolvent (1-θ) u (by linarith) (by linarith) hu
  have hev := euler_resolvent (1-θ) v (by linarith) (by linarith) hv
  have hsin : Real.sin (Real.pi*(1-θ)) = Real.sin (Real.pi*θ) := by
    rw [show Real.pi*(1-θ) = Real.pi - Real.pi*θ by ring, Real.sin_pi_sub]
  rw [hsin, show -(1-θ) = θ-1 by ring, Real.rpow_sub_one hu.ne'] at heu
  rw [hsin, show -(1-θ) = θ-1 by ring, Real.rpow_sub_one hv.ne'] at hev
  rw [heq, show -(1-θ) = θ-1 by ring]
  field_simp [sub_ne_zero.mpr huv, hu.ne', hv.ne', Real.pi_ne_zero] at heu hev ⊢
  nlinarith

/-- The confluent (equal-node) version of formula (2). -/
theorem power_divdiff_resolvent_diag (θ u : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hu : 0 < u) : θ * u ^ (θ-1) = Real.sin (Real.pi * θ) / Real.pi *
      ∫ t in Ioi (0:ℝ), t ^ θ / (u+t)^2 := by
  have hi : IntegrableOn (fun t => t^(θ-1)/(u+t)) (Ioi 0) := by
    simpa only [show -(1-θ) = θ-1 by ring] using
      euler_resolvent_integrable (1-θ) u (by linarith) (by linarith) hu
  have hii : IntegrableOn (fun t => t^θ/(u+t)^2) (Ioi 0) := by
    simpa only [pow_two] using power_divdiff_integrable θ u u hθ0 hθ1 hu hu
  have hd (t : ℝ) (ht : t ∈ Ioi 0) :
      HasDerivAt (fun t => t^θ/(u+t))
        (θ * (t^(θ-1)/(u+t)) - t^θ/(u+t)^2) t := by
    have ht : 0 < t := ht
    have hh := (Real.hasDerivAt_rpow_const (Or.inl ht.ne') (p := θ)).div
      ((hasDerivAt_const t u).add (hasDerivAt_id t)) (add_pos hu ht).ne'
    convert hh using 1 <;> (first | rfl | (dsimp; field_simp [(add_pos hu ht).ne']; ring))
  have hc : ContinuousWithinAt (fun t : ℝ => t^θ/(u+t)) (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hz : Filter.Tendsto (fun t : ℝ => t^θ/(u+t)) Filter.atTop (nhds 0) := by
    apply squeeze_zero' (g := fun t : ℝ => t^(θ-1))
    · filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
      positivity
    · filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
      rw [Real.rpow_sub_one ht.ne']
      gcongr
      linarith
    · simpa only [show -(1-θ) = θ-1 by ring] using
        tendsto_rpow_neg_atTop (by linarith : 0 < 1-θ)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hc hd ((hi.const_mul θ).sub hii) hz
  rw [MeasureTheory.integral_sub (hi.const_mul θ) hii,
    MeasureTheory.integral_const_mul, Real.zero_rpow hθ0.ne', zero_div, sub_zero] at hFTC
  have he := euler_resolvent (1-θ) u (by linarith) (by linarith) hu
  rw [show Real.pi*(1-θ) = Real.pi - Real.pi*θ by ring, Real.sin_pi_sub,
    show -(1-θ) = θ-1 by ring] at he
  rw [he]
  have hftc : (∫ t in Ioi (0:ℝ), t^θ/(u+t)^2) =
      θ * (∫ t in Ioi (0:ℝ), t^(θ-1)/(u+t)) := by linarith
  rw [hftc]
  ring

end D5.S3.Quantum.PositiveResolvent.EulerResolvent
