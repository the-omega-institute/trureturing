/- GID: D5/S3/Arith/Robin/OriginalFirstClockBufferEstimates
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/OriginalFirstClockBufferEstimates
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Consumed logarithmic density and integer deletion estimates for the original first-clock buffer. -/

import D5.S3.Arith.Robin.ActualRobinClockCovariance
import D5.S3.Arith.Robin.LogarithmBounds
import D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
import D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone

noncomputable section
open Classical

namespace D5.S3.Arith.Robin.OriginalFirstClockBufferEstimates

open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone

local notation "w₀" => D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity

/-- Backward comparison for the literal Robin activation density. -/
theorem buffer_density_left {x h : ℝ}
    (hx : 256 ≤ x) (hh : 0 < h) (hsmall : h ≤ x/20) :
    (81/100)*w₀ (x-h) ≤ w₀ x := by
  have hx0 : 0 < x := by linarith
  have hz : (19/20)*x ≤ x-h := by linarith
  have hz1 : 1 < x-h := by linarith
  have hz0 : 0 < x-h := by linarith
  have hlx : 1 < Real.log x :=
    (Real.lt_log_iff_exp_lt hx0).mpr
      (Real.exp_one_lt_three.trans_le (by linarith))
  have hlz0 : 0 < Real.log (x-h) := Real.log_pos hz1
  have hs := Real.log_le_sub_one_of_pos (div_pos hx0 hz0)
  rw [Real.log_div hx0.ne' hz0.ne'] at hs
  have hratio : x/(x-h)-1 ≤ 1/19 := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hz0).mpr
    linarith
  have hlz : (18/19)*Real.log x ≤ Real.log (x-h) := by linarith
  have hlmono : Real.log (x-h) ≤ Real.log x :=
    Real.log_le_log hz0 (by linarith)
  have hsqx : ((19/20)*x)^2 ≤ (x-h)^2 :=
    (sq_le_sq₀ (by positivity) hz0.le).mpr hz
  have hsql : ((18/19)*Real.log x)^2 ≤ (Real.log (x-h))^2 :=
    (sq_le_sq₀ (by positivity) hlz0.le).mpr hlz
  have hden : (81/100)*(x^2*(Real.log x)^2) ≤
      (x-h)^2*(Real.log (x-h))^2 := by
    have hm := mul_le_mul hsqx hsql (sq_nonneg _) (sq_nonneg _)
    convert! hm using 1 <;> ring
  have hdx : 0 < x^2*(Real.log x)^2 :=
    mul_pos (sq_pos_of_pos hx0) (sq_pos_of_pos (by linarith))
  have hdz : 0 < (x-h)^2*(Real.log (x-h))^2 :=
    mul_pos (sq_pos_of_pos hz0) (sq_pos_of_pos hlz0)
  change (81/100)*((Real.log (x-h)+1)/
      ((x-h)^2*(Real.log (x-h))^2)) ≤
    (Real.log x+1)/(x^2*(Real.log x)^2)
  rw [← mul_div_assoc, div_le_div_iff₀ hdz hdx]
  have hm := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ Real.log x+1 by linarith)
  have hn := mul_le_mul_of_nonneg_right
    (show Real.log (x-h)+1 ≤ Real.log x+1 by linarith)
    (show 0 ≤ (81/100)*(x^2*(Real.log x)^2) by positivity)
  nlinarith

/-- Strict forward comparison for the literal Robin activation density. -/
theorem buffer_density_right {x h : ℝ}
    (hx : 256 ≤ x) (hh : 0 < h) (hsmall : h ≤ x/20) :
    (81/100)*w₀ x < w₀ (x+h) := by
  have hx0 : 0 < x := by linarith
  have hz0 : 0 < x+h := by linarith
  have hlx : 1 < Real.log x :=
    (Real.lt_log_iff_exp_lt hx0).mpr
      (Real.exp_one_lt_three.trans_le (by linarith))
  have hz : x+h ≤ (21/20)*x := by linarith
  have hs := Real.log_le_sub_one_of_pos (div_pos hz0 hx0)
  rw [Real.log_div hz0.ne' hx0.ne'] at hs
  have hratio : (x+h)/x-1 ≤ 1/20 := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hx0).mpr
    linarith
  have hlz : Real.log (x+h) ≤ (21/20)*Real.log x := by linarith
  have hlmono : Real.log x ≤ Real.log (x+h) :=
    Real.log_le_log hx0 (by linarith)
  have hlz0 : 0 < Real.log (x+h) := by linarith
  have hsqx : (x+h)^2 ≤ ((21/20)*x)^2 :=
    (sq_le_sq₀ hz0.le (by positivity)).mpr hz
  have hsql : (Real.log (x+h))^2 ≤ ((21/20)*Real.log x)^2 :=
    (sq_le_sq₀ hlz0.le (by positivity)).mpr hlz
  have hden : (x+h)^2*(Real.log (x+h))^2 ≤
      (21/20)^4*(x^2*(Real.log x)^2) := by
    have hm := mul_le_mul hsqx hsql (sq_nonneg _) (sq_nonneg _)
    convert! hm using 1 <;> ring
  have hdx : 0 < x^2*(Real.log x)^2 :=
    mul_pos (sq_pos_of_pos hx0) (sq_pos_of_pos (by linarith))
  have hdz : 0 < (x+h)^2*(Real.log (x+h))^2 :=
    mul_pos (sq_pos_of_pos hz0) (sq_pos_of_pos hlz0)
  change (81/100)*((Real.log x+1)/(x^2*(Real.log x)^2)) <
    (Real.log (x+h)+1)/((x+h)^2*(Real.log (x+h))^2)
  rw [← mul_div_assoc, div_lt_div_iff₀ hdx hdz]
  have hm := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ (81/100)*(Real.log x+1) by positivity)
  have hn := mul_le_mul_of_nonneg_right
    (show Real.log x+1 ≤ Real.log (x+h)+1 by linarith) hdx.le
  have hc : (81/100)*(21/20)^4 < (1 : ℝ) := by norm_num
  nlinarith [mul_pos (sub_pos.mpr hc)
    (mul_pos (by linarith : 0 < Real.log x+1) hdx)]

/-- A legal nonlinear objective comparison bounds deletion by the first marginal.
The original consumer supplies the full forced-class maximality comparison. -/
theorem buffer_integer_removal_comparison {N q M : ℕ}
    (hM : 1 ≤ M) (hmul : M*q=N) (hq : q.Prime)
    (hbound :
      Real.log ((ArithmeticFunction.sigma 1 M : ℝ)/M) -
          Real.log (Real.log (Real.log (M : ℝ))) ≤
        Real.log ((ArithmeticFunction.sigma 1 N : ℝ)/N) -
          Real.log (Real.log (Real.log (N : ℝ)))) :
    Real.log (Real.log (Real.log (N : ℝ))) -
      Real.log (Real.log (Real.log (M : ℝ))) ≤ Real.log (1+1/(q : ℝ)) := by
  have hMq : 1 ≤ M*q := by nlinarith [hq.pos]
  have hd := golden_resource_objective_single_layer_delta 0 hM hq
  rw [golden_resource_sigma_identity 0 hMq,
    golden_resource_sigma_identity 0 hM] at hd
  simp only [zero_mul, sub_zero] at hd
  rw [hmul] at hd
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hmarg : goldenLayerMarginal q (M.factorization q+1) ≤ goldenLayerMarginal q 1 := by
    by_cases he : M.factorization q = 0
    · simp only [he, zero_add, le_refl]
    · exact (golden_layer_strict_decrease hq (by omega : 1 ≤ (1 : ℕ))
        (by omega : 1 < M.factorization q+1)).le
  have hfirst : goldenLayerMarginal q 1*Real.log (q : ℝ) =
      Real.log (1+1/(q : ℝ)) := by
    rw [golden_layer_marginal_one_eq_log_one_add_inv hq]
    exact div_mul_cancel₀ _ hlogq.ne'
  have hm := mul_le_mul_of_nonneg_right hmarg hlogq.le
  rw [hfirst] at hm
  linarith

#print axioms buffer_log_size
#print axioms buffer_density_left
#print axioms buffer_density_right
#print axioms buffer_integer_removal_comparison

end D5.S3.Arith.Robin.OriginalFirstClockBufferEstimates
