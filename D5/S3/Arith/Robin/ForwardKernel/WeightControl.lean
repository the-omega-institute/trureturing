/- GID: D5/S3/Arith/Robin/ForwardKernel/WeightControl
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/WeightControl
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The correlated forward weight ratio has a derivative smaller by the window scale. -/

import D5.S3.Arith.Robin.OriginalEarlyDivisorQuadrature
import D5.S3.Arith.Robin.ForwardKernel.ProfileKernelDefs
import Mathlib.Analysis.Calculus.MeanValue

namespace D5.S3.Arith.Robin.ForwardKernel.WeightControl

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open OriginalMovingWindowMoment (width)
open MellinWeightedVariation (weight)
open OriginalEarlyDivisorQuadrature (weightSlope)
open ProfileKernelDefs (priceRatio)

/-- The logarithmic derivative of the original positive price weight. -/
def logSlope (x : ℝ) : ℝ :=
  (-2 + (Real.log x + 1)⁻¹ - 2 * (Real.log x)⁻¹) / x

/-- The ratio keeps the same center in numerator and denominator. -/
def weightRatio (x u : ℝ) : ℝ := weight (x + u * width x) / weight x

/-- The price ratio is nonnegative and at most one for nonnegative displacements. -/
theorem price_bounds {x u : ℝ} (hx : 3 ≤ x) (hu : 0 ≤ u) :
    0 ≤ priceRatio x u ∧ priceRatio x u ≤ 1 := by
  have hx1 : 1 < x := by linarith
  have hy : x ≤ x + u := le_add_of_nonneg_right hu
  exact ⟨div_nonneg (MellinWeightedVariation.weight_nonneg (by linarith))
    (OriginalMovingWindowMoment.weight_pos hx1).le,
    (div_le_one (OriginalMovingWindowMoment.weight_pos hx1)).mpr
      (OriginalMovingWindowMoment.weight_antitone hx1 hy)⟩

private def slopeDerivative (x : ℝ) : ℝ :=
  (2 - (Real.log x + 1)⁻¹ - ((Real.log x + 1)⁻¹) ^ 2 +
    2 * (Real.log x)⁻¹ + 2 * ((Real.log x)⁻¹) ^ 2) / x ^ 2

private lemma inverse_log_bounds {x : ℝ} (hx : 4 ≤ x) :
    0 ≤ (Real.log x)⁻¹ ∧ (Real.log x)⁻¹ ≤ 1 ∧
      0 ≤ (Real.log x + 1)⁻¹ ∧ (Real.log x + 1)⁻¹ ≤ 1 := by
  have hl := OriginalMovingWindowMoment.log_large hx
  refine ⟨inv_nonneg.mpr (by linarith), ?_, inv_nonneg.mpr (by linarith), ?_⟩
  · exact (inv_le_one₀ (by linarith : 0 < Real.log x)).2 hl
  · exact (inv_le_one₀ (by linarith : 0 < Real.log x + 1)).2 (by linarith)

private lemma logSlope_eq {x : ℝ} (hx : 1 < x) :
    weightSlope x = weight x * logSlope x := by
  have hx0 : x ≠ 0 := ne_of_gt (by linarith)
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hl1 : Real.log x + 1 ≠ 0 := by positivity [Real.log_pos hx]
  unfold weightSlope MellinWeightedVariation.scaleDerivative weight logSlope
  simp only [mul_one, one_pow]
  field_simp [hx0, hl, hl1]
  <;> ring

private lemma logSlope_deriv {x : ℝ} (hx : 1 < x) :
    HasDerivAt logSlope (slopeDerivative x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (by linarith)
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hl1 : Real.log x + 1 ≠ 0 := by positivity [Real.log_pos hx]
  have hd := Real.hasDerivAt_log hx0
  have hd1 := (hd.add_const 1).inv hl1
  have hd0 := hd.inv hl
  have h := (((hasDerivAt_const x (-2 : ℝ)).add hd1).sub
    (hd0.const_mul 2)).div (hasDerivAt_id x) hx0
  convert h using 1
  · ext y
    simp [logSlope, mul_comm]
  · dsimp [slopeDerivative]
    field_simp [hx0, hl, hl1]
    <;> ring

private lemma logSlope_bound {x : ℝ} (hx : 4 ≤ x) : |logSlope x| ≤ 5 / x := by
  have hx0 : 0 < x := by linarith
  obtain ⟨ha, ha1, hb, hb1⟩ := inverse_log_bounds hx
  unfold logSlope
  rw [abs_div, abs_of_pos hx0]
  apply div_le_div_of_nonneg_right _ hx0.le
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma slopeDerivative_bound {x : ℝ} (hx : 4 ≤ x) :
    |slopeDerivative x| ≤ 8 / x ^ 2 := by
  obtain ⟨ha, ha1, hb, hb1⟩ := inverse_log_bounds hx
  have ha2 : (Real.log x)⁻¹ ^ 2 ≤ 1 := by nlinarith
  have hb2 : (Real.log x + 1)⁻¹ ^ 2 ≤ 1 := by nlinarith
  unfold slopeDerivative
  rw [abs_div, abs_of_nonneg (sq_nonneg x)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg x)
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg ((Real.log x)⁻¹)],
    by nlinarith [sq_nonneg ((Real.log x + 1)⁻¹)]⟩

private lemma logSlope_lipschitz {x y : ℝ} (hx : 4 ≤ x) (hxy : x ≤ y) :
    |logSlope y - logSlope x| ≤ (8 / x ^ 2) * (y - x) := by
  have hx0 : 0 < x := by linarith
  have hd : ∀ z ∈ Icc x y, HasDerivWithinAt logSlope (slopeDerivative z) (Icc x y) z :=
    fun z hz => (logSlope_deriv (by linarith [hz.1])).hasDerivWithinAt
  have hb : ∀ z ∈ Icc x y, ‖slopeDerivative z‖ ≤ 8 / x ^ 2 := by
    intro z hz
    rw [Real.norm_eq_abs]
    calc
      _ ≤ 8 / z ^ 2 := slopeDerivative_bound (hx.trans hz.1)
      _ ≤ 8 / x ^ 2 := by gcongr; exact hz.1
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc x y)
    (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] using h

private lemma width_div {x : ℝ} (hx : 0 < x) : width x / x = x ^ (-1 / 5 : ℝ) := by
  unfold width
  calc
    x ^ (4 / 5 : ℝ) / x = x ^ (4 / 5 : ℝ) / x ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = x ^ ((4 / 5 : ℝ) - 1) := (Real.rpow_sub hx _ _).symm
    _ = x ^ (-1 / 5 : ℝ) := by norm_num

private lemma priceRatio_deriv {θ x s : ℝ} (hx : 1 < x) (hs : 0 ≤ s) :
    HasDerivAt (fun y => priceRatio y (s * y ^ θ))
      (priceRatio x (s * x ^ θ) *
        (logSlope (x + s * x ^ θ) * (1 + θ * s * x ^ (θ - 1)) -
          logSlope x)) x := by
  have hx0 : 0 < x := by linarith
  have hy : 1 < x + s * x ^ θ := by
    have hp : 0 ≤ s * x ^ θ := mul_nonneg hs (Real.rpow_nonneg hx0.le _)
    linarith
  have hw := OriginalMovingWindowMoment.weight_pos hx
  have hdw := OriginalEarlyDivisorQuadrature.weight_deriv hx
  have hdwy := OriginalEarlyDivisorQuadrature.weight_deriv hy
  have hdx := Real.hasDerivAt_rpow_const (p := θ) (Or.inl hx0.ne')
  have hdy : HasDerivAt (fun y => y + s * y ^ θ)
      (1 + θ * s * x ^ (θ - 1)) x := by
    convert (hasDerivAt_id x).add (hdx.const_mul s) using 1 <;>
      first | rfl | ring
  have h := (hdwy.comp x hdy).div hdw hw.ne'
  convert h using 1
  · rfl
  · rw [logSlope_eq hx, logSlope_eq hy]
    unfold priceRatio
    simp only [Function.comp_apply]
    field_simp [hw.ne']
    <;> ring

/-- The price ratio differs from one by at most four times the relative displacement. -/
theorem priceRatio_sub_one {x u : ℝ} (hx : 4 ≤ x) (hu : 0 ≤ u) :
    0 ≤ 1 - priceRatio x u ∧ 1 - priceRatio x u ≤ 4 * u / x := by
  have hx0 : 0 < x := by linarith
  let y := x + u
  have hxy : x ≤ y := le_add_of_nonneg_right hu
  have hy0 : 0 < y := hx0.trans_le hxy
  have hw := OriginalMovingWindowMoment.weight_pos (by linarith : 1 < x)
  have hr : priceRatio x u ≤ 1 :=
    (div_le_one hw).2 (OriginalMovingWindowMoment.weight_antitone (by linarith) hxy)
  have hlo : (x / y) ^ 4 ≤ priceRatio x u :=
    (le_div_iff₀ hw).2 (OriginalMovingWindowMoment.weight_ratio_lower hx hxy)
  have hδ : 0 ≤ (y - x) / x := div_nonneg (sub_nonneg.mpr hxy) hx0.le
  have hpower := OriginalMovingWindowMoment.negative_power_lower hδ (by norm_num : (0 : ℝ) ≤ 4)
  have heq : 1 + (y - x) / x = y / x := by field_simp; ring
  rw [heq, Real.rpow_neg (div_pos hy0 hx0).le, show (4 : ℝ) = (4 : ℕ) by norm_num,
    Real.rpow_natCast] at hpower
  have hrel : 1 - (x / y) ^ 4 ≤ 4 * ((y - x) / x) := by
    rw [div_pow, inv_div] at hpower
    rw [div_pow]
    linarith
  refine ⟨by linarith, ?_⟩
  calc
    _ ≤ 1 - (x / y) ^ 4 := by linarith
    _ ≤ 4 * ((y - x) / x) := hrel
    _ = 4 * u / x := by dsimp [y]; ring

/-- The value of the correlated ratio differs from one by the relative window length. -/
theorem weightRatio_sub_one {x u : ℝ} (hx : 4 ≤ x) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    |weightRatio x u - 1| ≤ 4 * x ^ (-1 / 5 : ℝ) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨h0, h1⟩ := priceRatio_sub_one hx
    (show 0 ≤ u * width x from mul_nonneg hu (Real.rpow_nonneg hx0.le _))
  change |priceRatio x (u * width x) - 1| ≤ _
  rw [abs_of_nonpos (by linarith : priceRatio x (u * width x) - 1 ≤ 0)]
  calc
    _ ≤ 4 * (u * width x) / x := by linarith
    _ = 4 * u * x ^ (-1 / 5 : ℝ) := by rw [mul_assoc, mul_div_assoc, mul_div_assoc, width_div hx0]
    _ ≤ 4 * x ^ (-1 / 5 : ℝ) := by
      nlinarith [Real.rpow_pos_of_pos hx0 (-1 / 5 : ℝ)]

/-- The correlated price ratio at any positive sublinear power has a uniformly
bounded value and a derivative with an additional relative-window factor. -/
theorem priceRatio_control {θ x s : ℝ} (hθ : 0 < θ)
    (hx : 4 ≤ x) (hs : 0 ≤ s) :
    0 ≤ priceRatio x (s * x ^ θ) ∧ priceRatio x (s * x ^ θ) ≤ 1 ∧
      HasDerivAt (fun y => priceRatio y (s * y ^ θ))
        (priceRatio x (s * x ^ θ) *
          (logSlope (x + s * x ^ θ) * (1 + θ * s * x ^ (θ - 1)) -
            logSlope x)) x ∧
      |priceRatio x (s * x ^ θ) *
        (logSlope (x + s * x ^ θ) * (1 + θ * s * x ^ (θ - 1)) -
          logSlope x)| ≤ (8 + 5 * θ) * s * x ^ (θ - 2) := by
  have hx0 : 0 < x := by linarith
  let y := x + s * x ^ θ
  have hxy : x ≤ y := by
    dsimp [y]
    exact le_add_of_nonneg_right (mul_nonneg hs (Real.rpow_nonneg hx0.le _))
  have hy4 : 4 ≤ y := hx.trans hxy
  obtain ⟨hratio0, hratio1⟩ := price_bounds (by linarith : 3 ≤ x)
    (mul_nonneg hs (Real.rpow_nonneg hx0.le _))
  refine ⟨hratio0, hratio1, priceRatio_deriv (by linarith) hs, ?_⟩
  have hlog : |logSlope y| ≤ 5 / x := (logSlope_bound hy4).trans (by gcongr)
  have hdiff := logSlope_lipschitz hx hxy
  have hp : 0 ≤ θ * s * x ^ (θ - 1) := by positivity
  have he : y - x = s * x ^ θ := by dsimp [y]; ring
  have hmain : |logSlope y * (1 + θ * s * x ^ (θ - 1)) - logSlope x| ≤
      (8 + 5 * θ) * s * x ^ (θ - 2) := by
    calc
      _ = |(logSlope y - logSlope x) +
          logSlope y * (θ * s * x ^ (θ - 1))| := by congr 1; ring
      _ ≤ |logSlope y - logSlope x| +
          |logSlope y * (θ * s * x ^ (θ - 1))| := abs_add_le _ _
      _ ≤ (8 / x ^ 2) * (y - x) + (5 / x) * (θ * s * x ^ (θ - 1)) := by
        rw [abs_mul, abs_of_nonneg hp]
        exact add_le_add hdiff (mul_le_mul_of_nonneg_right hlog hp)
      _ = (8 + 5 * θ) * s * x ^ (θ - 2) := by
        have hpow : x ^ θ / x ^ 2 = x ^ (θ - 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_sub hx0]
          norm_num
        have hpow' : x ^ (θ - 1) / x = x ^ (θ - 2) := by
          calc
            _ = x ^ (θ - 1) / x ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = x ^ ((θ - 1) - 1) := (Real.rpow_sub hx0 _ _).symm
            _ = _ := by congr 1; ring
        rw [he]
        calc
          _ = 8 * s * (x ^ θ / x ^ 2) + 5 * θ * s * (x ^ (θ - 1) / x) := by ring
          _ = _ := by rw [hpow, hpow']; ring
  rw [abs_mul, abs_of_nonneg hratio0]
  exact (mul_le_mul_of_nonneg_left hmain hratio0).trans
    (mul_le_of_le_one_left (by positivity) hratio1)

/-- Differentiating the correlated ratio cancels the order 1/x terms.
The remaining derivative has the additional x^(-1/5) window factor. -/
theorem weightRatio_control {x u : ℝ} (hx : 4 ≤ x) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ weightRatio x u ∧ weightRatio x u ≤ 1 ∧
      HasDerivAt (fun y => weightRatio y u)
        (weightRatio x u *
          (logSlope (x + u * width x) * (1 + (4 / 5 : ℝ) * u * x ^ (-1 / 5 : ℝ)) -
            logSlope x)) x ∧
      |weightRatio x u *
        (logSlope (x + u * width x) * (1 + (4 / 5 : ℝ) * u * x ^ (-1 / 5 : ℝ)) -
          logSlope x)| ≤ 12 * x ^ (-6 / 5 : ℝ) := by
  obtain ⟨h0, h1, hd, hb⟩ := priceRatio_control
    (θ := (4 / 5 : ℝ)) (by norm_num) hx hu
  rw [show (4 / 5 : ℝ) - 1 = -1 / 5 by norm_num] at hd hb
  rw [show (8 + 5 * (4 / 5) : ℝ) = 12 by norm_num,
    show (4 / 5 : ℝ) - 2 = -6 / 5 by norm_num] at hb
  refine ⟨h0, h1, hd, hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith : 12 * u ≤ 12)
    (Real.rpow_nonneg (by linarith) _)

#print axioms weightRatio_control

end
end D5.S3.Arith.Robin.ForwardKernel.WeightControl
