/- GID: D5/S3/Analytic/ExponentialSum/TwoScaleEndpointMoments
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:uniform-exponential-moment-estimate)
   anchors: []
   utility: none
   digest: Uniform moments in the full two-scale exponential span. -/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

/-! Uniform moments for signed two-scale exponential families and their endpoint rescalings. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace TwoScaleEndpointMoments
open MeasureTheory Set

/-- The entire two-dimensional exponential span, including signed cancellation. -/
def twoScaleShape (a b t : ℝ) : ℝ :=
  a * Real.exp (-t) + b * Real.exp (-(2 * t))

private theorem exponential_moment (r : ℝ) (hr : 0 < r) (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(r * t))) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, t ^ k * Real.exp (-(r * t))) =
        (k.factorial : ℝ) / r ^ (k + 1) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (k : ℝ)) (p := 1) (b := r)
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg k)) (by norm_num) hr
  have hv := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := ((k + 1 : ℕ) : ℝ)) (r := r) (by positivity) hr
  have hk : ((k + 1 : ℕ) : ℝ) - 1 = (k : ℝ) := by push_cast; ring
  rw [hk] at hv
  simp only [Real.rpow_natCast] at hv
  refine ⟨?_, ?_⟩
  · simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using hi
  · simpa only [Real.rpow_natCast, Nat.cast_add, Nat.cast_one,
      Real.Gamma_nat_eq_factorial, one_div, inv_pow, mul_comm, div_eq_mul_inv,
      mul_one, one_mul] using hv

private theorem shape_moment (a b : ℝ) (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k * twoScaleShape a b t ^ 2) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, t ^ k * twoScaleShape a b t ^ 2) =
        a ^ 2 * ((k.factorial : ℝ) / 2 ^ (k + 1)) +
        (2 * a * b) * ((k.factorial : ℝ) / 3 ^ (k + 1)) +
        b ^ 2 * ((k.factorial : ℝ) / 4 ^ (k + 1)) := by
  have h2 := exponential_moment 2 (by norm_num) k
  have h3 := exponential_moment 3 (by norm_num) k
  have h4 := exponential_moment 4 (by norm_num) k
  have he (t : ℝ) : t ^ k * twoScaleShape a b t ^ 2 =
      a ^ 2 * (t ^ k * Real.exp (-(2 * t))) +
      (2 * a * b) * (t ^ k * Real.exp (-(3 * t))) +
      b ^ 2 * (t ^ k * Real.exp (-(4 * t))) := by
    have e2 : Real.exp (-t) * Real.exp (-t) = Real.exp (-(2 * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e3 : Real.exp (-t) * Real.exp (-(2 * t)) = Real.exp (-(3 * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e4 : Real.exp (-(2 * t)) * Real.exp (-(2 * t)) = Real.exp (-(4 * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = a ^ 2 * (t ^ k * (Real.exp (-t) * Real.exp (-t))) +
          (2 * a * b) * (t ^ k * (Real.exp (-t) * Real.exp (-(2 * t)))) +
          b ^ 2 * (t ^ k * (Real.exp (-(2 * t)) * Real.exp (-(2 * t)))) := by
        unfold twoScaleShape
        ring
      _ = _ := by rw [e2, e3, e4]
  have hi2 : IntegrableOn (fun t : ℝ => a ^ 2 * (t ^ k * Real.exp (-(2 * t))))
      (Ioi 0) := h2.1.const_mul _
  have hi3 : IntegrableOn (fun t : ℝ => (2 * a * b) * (t ^ k * Real.exp (-(3 * t))))
      (Ioi 0) := h3.1.const_mul _
  have hi4 : IntegrableOn (fun t : ℝ => b ^ 2 * (t ^ k * Real.exp (-(4 * t))))
      (Ioi 0) := h4.1.const_mul _
  have hi23 : IntegrableOn (fun t : ℝ => a ^ 2 * (t ^ k * Real.exp (-(2 * t))) +
      (2 * a * b) * (t ^ k * Real.exp (-(3 * t)))) (Ioi 0) := hi2.add hi3
  have hi := hi23.add hi4
  refine ⟨hi.congr (Filter.Eventually.of_forall fun t => (he t).symm), ?_⟩
  calc
    _ = ∫ t : ℝ in Ioi 0,
        a ^ 2 * (t ^ k * Real.exp (-(2 * t))) +
        (2 * a * b) * (t ^ k * Real.exp (-(3 * t))) +
        b ^ 2 * (t ^ k * Real.exp (-(4 * t))) := by
      exact integral_congr_ae (Filter.Eventually.of_forall he)
    _ = _ := by
      rw [integral_add hi23 hi4, integral_add hi2 hi3,
        integral_const_mul, integral_const_mul, integral_const_mul, h2.2, h3.2, h4.2]

private theorem shape_moment_upper (a b : ℝ) (k : ℕ) :
    (∫ t : ℝ in Ioi 0, t ^ k * twoScaleShape a b t ^ 2) ≤
      (k.factorial : ℝ) * (a ^ 2 + b ^ 2) := by
  have h2 : (2 : ℝ) ≤ 2 ^ (k + 1) := by
    rw [pow_succ]
    nlinarith [one_le_pow₀ (n := k) (by norm_num : (1 : ℝ) ≤ 2)]
  have h3 : (3 : ℝ) ≤ 3 ^ (k + 1) := by
    rw [pow_succ]
    nlinarith [one_le_pow₀ (n := k) (by norm_num : (1 : ℝ) ≤ 3)]
  have h4 : (4 : ℝ) ≤ 4 ^ (k + 1) := by
    rw [pow_succ]
    nlinarith [one_le_pow₀ (n := k) (by norm_num : (1 : ℝ) ≤ 4)]
  have ha := div_le_div_of_nonneg_left (sq_nonneg a) (by norm_num : (0 : ℝ) < 2) h2
  have hb := div_le_div_of_nonneg_left (sq_nonneg b) (by norm_num : (0 : ℝ) < 4) h4
  have hab : 2 * a * b ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have hc := (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 3 ^ (k + 1))).2 hab
  have hd := div_le_div_of_nonneg_left (add_nonneg (sq_nonneg a) (sq_nonneg b))
    (by norm_num : (0 : ℝ) < 3) h3
  rw [(shape_moment a b k).2]
  have he : a ^ 2 * ((k.factorial : ℝ) / 2 ^ (k + 1)) +
      (2 * a * b) * ((k.factorial : ℝ) / 3 ^ (k + 1)) +
      b ^ 2 * ((k.factorial : ℝ) / 4 ^ (k + 1)) =
      (k.factorial : ℝ) *
        (a ^ 2 / 2 ^ (k + 1) + (2 * a * b) / 3 ^ (k + 1) +
          b ^ 2 / 4 ^ (k + 1)) := by ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k.factorial)
  nlinarith [sq_nonneg a, sq_nonneg b]

/-- Every signed coefficient pair has a uniform moment bound relative to its
own mass. The Gram coercivity prevents coefficient cancellation from defeating
the estimate; no coefficient ratio or noncancellation premise is assumed. -/
private theorem two_scale_uniform_moment (a b : ℝ) (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k * twoScaleShape a b t ^ 2) (Ioi 0) ∧
      (a ^ 2 + b ^ 2) / 54 ≤
        (∫ t : ℝ in Ioi 0, twoScaleShape a b t ^ 2) ∧
      (∫ t : ℝ in Ioi 0, t ^ k * twoScaleShape a b t ^ 2) ≤
        54 * (k.factorial : ℝ) *
          (∫ t : ℝ in Ioi 0, twoScaleShape a b t ^ 2) := by
  have h0 := (shape_moment a b 0).2
  norm_num at h0
  have hgram : a ^ 2 + b ^ 2 ≤
      54 * (∫ t : ℝ in Ioi 0, twoScaleShape a b t ^ 2) := by
    rw [h0]
    nlinarith [sq_nonneg (26 * a + 18 * b), sq_nonneg b]
  refine ⟨(shape_moment a b k).1, ?_, ?_⟩
  · exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 54)).2 (by nlinarith [hgram])
  · calc
      _ ≤ (k.factorial : ℝ) * (a ^ 2 + b ^ 2) := shape_moment_upper a b k
      _ ≤ (k.factorial : ℝ) *
          (54 * (∫ t : ℝ in Ioi 0, twoScaleShape a b t ^ 2)) :=
        mul_le_mul_of_nonneg_left hgram (Nat.cast_nonneg k.factorial)
      _ = _ := by ring


/-- The two-scale family centered at an arbitrary endpoint. -/
def twoScaleEndpoint (a b endpoint p x : ℝ) : ℝ :=
  twoScaleShape a b (p * (x - endpoint))

private theorem translate_scale (h : ℝ → ℝ) (endpoint p : ℝ) (hp : 0 < p)
    (hi : IntegrableOn h (Ioi 0)) :
    IntegrableOn (fun x : ℝ => h (p * (x - endpoint))) (Ioi endpoint) ∧
      (∫ x : ℝ in Ioi endpoint, h (p * (x - endpoint))) =
        p⁻¹ * (∫ t : ℝ in Ioi 0, h t) := by
  classical
  have hs : IntegrableOn (fun t : ℝ => h (p * t)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff h 0 hp).2
    simpa only [mul_zero] using hi
  have he : (Ioi endpoint).indicator (fun x : ℝ => h (p * (x - endpoint))) =
      (fun x : ℝ => (Ioi 0).indicator (fun t : ℝ => h (p * t)) (x - endpoint)) := by
    funext x
    simp only [Set.indicator, mem_Ioi, sub_pos]
  have hind : Integrable ((Ioi 0).indicator (fun t : ℝ => h (p * t))) :=
    (integrable_indicator_iff measurableSet_Ioi).2 hs
  have ht := hind.comp_sub_right endpoint
  rw [← he] at ht
  refine ⟨(integrable_indicator_iff measurableSet_Ioi).1 ht, ?_⟩
  calc
    _ = ∫ x : ℝ, (Ioi endpoint).indicator
        (fun y : ℝ => h (p * (y - endpoint))) x :=
      (integral_indicator measurableSet_Ioi).symm
    _ = ∫ x : ℝ, (Ioi 0).indicator (fun t : ℝ => h (p * t)) (x - endpoint) := by
      rw [he]
    _ = ∫ t : ℝ, (Ioi 0).indicator (fun t : ℝ => h (p * t)) t :=
      integral_sub_right_eq_self _ endpoint
    _ = ∫ t : ℝ in Ioi 0, h (p * t) := integral_indicator measurableSet_Ioi
    _ = _ := by
      simpa only [mul_zero, smul_eq_mul] using integral_comp_mul_left_Ioi h 0 hp

private theorem endpoint_moment_value
    (a b endpoint p : ℝ) (hp : 0 < p) (k : ℕ) :
    IntegrableOn (fun x : ℝ => (x - endpoint) ^ k *
      twoScaleEndpoint a b endpoint p x ^ 2) (Ioi endpoint) ∧
      (∫ x : ℝ in Ioi endpoint, (x - endpoint) ^ k *
        twoScaleEndpoint a b endpoint p x ^ 2) =
        (p ^ k)⁻¹ * (p⁻¹ *
          (∫ t : ℝ in Ioi 0, t ^ k * twoScaleShape a b t ^ 2)) := by
  have hs := translate_scale (fun t : ℝ => t ^ k * twoScaleShape a b t ^ 2)
    endpoint p hp (shape_moment a b k).1
  have he (x : ℝ) : (x - endpoint) ^ k * twoScaleEndpoint a b endpoint p x ^ 2 =
      (p ^ k)⁻¹ * ((p * (x - endpoint)) ^ k *
        twoScaleShape a b (p * (x - endpoint)) ^ 2) := by
    dsimp only [twoScaleEndpoint]
    rw [mul_pow]
    field_simp [pow_ne_zero k hp.ne']
  refine ⟨(hs.1.const_mul ((p ^ k)⁻¹)).congr
    (Filter.Eventually.of_forall fun x => (he x).symm), ?_⟩
  calc
    _ = ∫ x : ℝ in Ioi endpoint,
        (p ^ k)⁻¹ * ((p * (x - endpoint)) ^ k *
          twoScaleShape a b (p * (x - endpoint)) ^ 2) :=
      integral_congr_ae (Filter.Eventually.of_forall he)
    _ = _ := by rw [integral_const_mul, hs.2]

/-- All moments in the full two-dimensional endpoint family are uniformly
bounded by its own mass. The factor p⁻ᵏ gives concentration at the endpoint,
including coefficient choices that depend on p and exhibit cancellation. -/
theorem two_scale_endpoint_moment_bound
    (a b endpoint p : ℝ) (hp : 0 < p) (k : ℕ) :
    IntegrableOn (fun x : ℝ => (x - endpoint) ^ k *
      twoScaleEndpoint a b endpoint p x ^ 2) (Ioi endpoint) ∧
      (a ^ 2 + b ^ 2) / (54 * p) ≤
        (∫ x : ℝ in Ioi endpoint, twoScaleEndpoint a b endpoint p x ^ 2) ∧
      (∫ x : ℝ in Ioi endpoint, (x - endpoint) ^ k *
        twoScaleEndpoint a b endpoint p x ^ 2) ≤
        (54 * (k.factorial : ℝ) / p ^ k) *
          (∫ x : ℝ in Ioi endpoint, twoScaleEndpoint a b endpoint p x ^ 2) := by
  have hshape := two_scale_uniform_moment a b k
  have hi0 : IntegrableOn (fun t : ℝ => twoScaleShape a b t ^ 2) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using (shape_moment a b 0).1
  have hD : (∫ x : ℝ in Ioi endpoint, twoScaleEndpoint a b endpoint p x ^ 2) =
      p⁻¹ * (∫ t : ℝ in Ioi 0, twoScaleShape a b t ^ 2) := by
    simpa only [twoScaleEndpoint] using (translate_scale
      (fun t : ℝ => twoScaleShape a b t ^ 2) endpoint p hp hi0).2
  have hvalue := endpoint_moment_value a b endpoint p hp k
  refine ⟨hvalue.1, ?_, ?_⟩
  · calc
      _ = p⁻¹ * ((a ^ 2 + b ^ 2) / 54) := by
        field_simp [hp.ne']
      _ ≤ p⁻¹ * (∫ t : ℝ in Ioi 0, twoScaleShape a b t ^ 2) :=
        mul_le_mul_of_nonneg_left hshape.2.1 (inv_nonneg.mpr hp.le)
      _ = _ := hD.symm
  · rw [hvalue.2]
    calc
      _ ≤ (p ^ k)⁻¹ * (p⁻¹ *
          (54 * (k.factorial : ℝ) * (∫ t : ℝ in Ioi 0, twoScaleShape a b t ^ 2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hshape.2.2 (inv_nonneg.mpr hp.le))
          (inv_nonneg.mpr (pow_nonneg hp.le k))
      _ = _ := by rw [hD]; ring

end TwoScaleEndpointMoments
