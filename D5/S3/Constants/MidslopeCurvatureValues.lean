/- GID: D5/S3/Constants/MidslopeCurvatureValues
   generality: G
   mirror-B: D5/B/S3/Constants/MidslopeCurvatureValues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Evaluate the remaining rationalizable midslope-curvature integrals exactly. -/

import D5.S3.Constants.MidslopeCurvature

open scoped Interval

namespace D5.S3.Constants.MidslopeCurvatureValues

open D5.S3.Constants.MidslopeCurvature
open D5.S3.Constants.PowerMeanKernel

/-- The midslope-curvature integral specialized to the power mean at parameter `-1/2`. -/
noncomputable def J_neg_half : ℝ :=
  ∫ t in (0 : ℝ)..1,
    ((1 - t) / t ^ 2) *
      (1 / (2 * meanNegHalf ((1 + t) / 2) ((1 - t) / 2)) - 1 / (1 - t ^ 2))

/-- The midslope-curvature integral specialized to the geometric mean. -/
noncomputable def J_zero : ℝ :=
  ∫ t in (0 : ℝ)..1,
    ((1 - t) / t ^ 2) *
      (1 / (2 * meanZero ((1 + t) / 2) ((1 - t) / 2)) - 1 / (1 - t ^ 2))

/-- The midslope-curvature integral specialized to the power mean at parameter `1/2`. -/
noncomputable def J_half : ℝ :=
  ∫ t in (0 : ℝ)..1,
    ((1 - t) / t ^ 2) *
      (1 / (2 * meanHalf ((1 + t) / 2) ((1 - t) / 2)) - 1 / (1 - t ^ 2))

private noncomputable def weierstrass (u : ℝ) : ℝ := 2 * u / (1 + u ^ 2)

private noncomputable def weierstrassDeriv (u : ℝ) : ℝ :=
  2 * (1 - u ^ 2) / (1 + u ^ 2) ^ 2

private theorem hasDerivAt_weierstrass (u : ℝ) :
    HasDerivAt weierstrass (weierstrassDeriv u) u := by
  unfold weierstrass weierstrassDeriv
  have hnum : HasDerivAt (fun x : ℝ => 2 * x) 2 u := by
    simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
  have hden : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * u) u := by
    simpa using ((hasDerivAt_id u).pow 2).const_add (1 : ℝ)
  have hden_ne : 1 + u ^ 2 ≠ 0 := by nlinarith [sq_nonneg u]
  have hderiv :
      2 * (1 - u ^ 2) / (1 + u ^ 2) ^ 2 =
        (2 * (1 + u ^ 2) - 2 * u * (2 * u)) / (1 + u ^ 2) ^ 2 := by
    ring
  rw [hderiv]
  exact hnum.fun_div (𝕜 := ℝ) (𝕜' := ℝ) hden hden_ne

private theorem integral_weierstrass (g : ℝ → ℝ) :
    (∫ t in (0 : ℝ)..1, g t) =
      ∫ u in (0 : ℝ)..1, g (weierstrass u) * weierstrassDeriv u := by
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := 1) (f := weierstrass) (f' := weierstrassDeriv) (g := g)
    (by
      unfold weierstrass
      have hnum : Continuous (fun u : ℝ => 2 * u) := by fun_prop
      have hden : Continuous (fun u : ℝ => 1 + u ^ 2) := by fun_prop
      exact (hnum.div hden (fun u => by nlinarith [sq_nonneg u])).continuousOn)
    (fun u _hu => hasDerivAt_weierstrass u)
    (fun u hu => by
      norm_num at hu
      have hnum : 0 ≤ 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
      unfold weierstrassDeriv
      exact div_nonneg (mul_nonneg (by norm_num) hnum) (sq_nonneg _))
  norm_num [weierstrass] at hsub
  exact hsub.symm

/-- The negative-half integrand is pointwise half the geometric-mean integrand. -/
theorem J_neg_half_eq_half_J_zero : J_neg_half = J_zero / 2 := by
  rw [J_neg_half, J_zero]
  calc
    _ = ∫ t in (0 : ℝ)..1,
        (((1 - t) / t ^ 2) *
          (1 / (2 * meanZero ((1 + t) / 2) ((1 - t) / 2)) - 1 / (1 - t ^ 2))) / 2 := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      have ht_pos : 0 < t := ht.1
      have ht_lt : t < 1 := ht.2
      have ha : 0 ≤ (1 + t) / 2 := by linarith
      have hb : 0 ≤ (1 - t) / 2 := by linarith
      have hsquare : 0 < 1 - t ^ 2 := by
        nlinarith [mul_pos (sub_pos.mpr ht_lt) (by linarith : 0 < 1 + t)]
      have hsqrt_product :
          Real.sqrt (((1 + t) / 2) * ((1 - t) / 2)) =
            Real.sqrt (1 - t ^ 2) / 2 := by
        rw [show ((1 + t) / 2) * ((1 - t) / 2) = (1 - t ^ 2) / 4 by ring]
        rw [Real.sqrt_div hsquare.le]
        have hsqrt_four : Real.sqrt (4 : ℝ) = 2 := by
          have hsquare_four := Real.sq_sqrt (show (0 : ℝ) ≤ 4 by norm_num)
          have hnonneg_four := Real.sqrt_nonneg (4 : ℝ)
          nlinarith
        rw [hsqrt_four]
      have hzero :
          2 * meanZero ((1 + t) / 2) ((1 - t) / 2) = Real.sqrt (1 - t ^ 2) := by
        rw [meanZero, hsqrt_product]
        ring
      have hsqrt_sum :
          (Real.sqrt ((1 + t) / 2) + Real.sqrt ((1 - t) / 2)) ^ 2 =
            1 + Real.sqrt (1 - t ^ 2) := by
        have hproduct :
            Real.sqrt ((1 + t) / 2) * Real.sqrt ((1 - t) / 2) =
              Real.sqrt (1 - t ^ 2) / 2 := by
          rw [← Real.sqrt_mul ha, hsqrt_product]
        rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
        calc
          (1 + t) / 2 + 2 * Real.sqrt ((1 + t) / 2) * Real.sqrt ((1 - t) / 2) +
                (1 - t) / 2 =
              (1 + t) / 2 +
                2 * (Real.sqrt ((1 + t) / 2) * Real.sqrt ((1 - t) / 2)) +
                (1 - t) / 2 := by ring
          _ = 1 + Real.sqrt (1 - t ^ 2) := by rw [hproduct]; ring
      have hsqrt_square : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 :=
        Real.sq_sqrt hsquare.le
      have hneg_half :
          2 * meanNegHalf ((1 + t) / 2) ((1 - t) / 2) =
            2 * (1 - t ^ 2) / (1 + Real.sqrt (1 - t ^ 2)) := by
        rw [meanNegHalf, hsqrt_sum]
        ring
      change
        (1 - t) / t ^ 2 *
            (1 / (2 * meanNegHalf ((1 + t) / 2) ((1 - t) / 2)) - 1 / (1 - t ^ 2)) =
          ((1 - t) / t ^ 2 *
            (1 / (2 * meanZero ((1 + t) / 2) ((1 - t) / 2)) - 1 / (1 - t ^ 2))) / 2
      rw [hzero, hneg_half]
      have hsqrt_pos : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.2 hsquare
      field_simp [ne_of_gt ht_pos, ne_of_gt hsquare, ne_of_gt hsqrt_pos]
      nlinarith [hsqrt_square]
    _ = (∫ t in (0 : ℝ)..1,
        ((1 - t) / t ^ 2) *
          (1 / (2 * meanZero ((1 + t) / 2) ((1 - t) / 2)) - 1 / (1 - t ^ 2))) / 2 := by
      rw [intervalIntegral.integral_div]

/-- The geometric-mean midslope curvature is `1 - 2 * log 2`. -/
theorem J_zero_eq_one_sub_two_log_two : J_zero = 1 - 2 * Real.log 2 := by
  rw [J_zero]
  calc
    _ = ∫ t in (0 : ℝ)..1,
        -(1 / ((1 + t) * (1 + Real.sqrt (1 - t ^ 2)))) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      have ht_pos : 0 < t := ht.1
      have ht_lt : t < 1 := ht.2
      have hsquare : 0 < 1 - t ^ 2 := by
        nlinarith [mul_pos (sub_pos.mpr ht_lt) (by linarith : 0 < 1 + t)]
      have hsqrt_product :
          Real.sqrt (((1 + t) / 2) * ((1 - t) / 2)) =
            Real.sqrt (1 - t ^ 2) / 2 := by
        rw [show ((1 + t) / 2) * ((1 - t) / 2) = (1 - t ^ 2) / 4 by ring]
        rw [Real.sqrt_div hsquare.le]
        have hsqrt_four : Real.sqrt (4 : ℝ) = 2 := by
          have hsquare_four := Real.sq_sqrt (show (0 : ℝ) ≤ 4 by norm_num)
          have hnonneg_four := Real.sqrt_nonneg (4 : ℝ)
          nlinarith
        rw [hsqrt_four]
      have hzero :
          2 * meanZero ((1 + t) / 2) ((1 - t) / 2) = Real.sqrt (1 - t ^ 2) := by
        rw [meanZero, hsqrt_product]
        ring
      have hsqrt_square : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 :=
        Real.sq_sqrt hsquare.le
      change
        (1 - t) / t ^ 2 *
            (1 / (2 * meanZero ((1 + t) / 2) ((1 - t) / 2)) - 1 / (1 - t ^ 2)) =
          -(1 / ((1 + t) * (1 + Real.sqrt (1 - t ^ 2))))
      rw [hzero]
      have hsqrt_pos : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.2 hsquare
      field_simp [ne_of_gt ht_pos, ne_of_gt hsquare, ne_of_gt hsqrt_pos]
      nlinarith [hsqrt_square]
    _ = ∫ u in (0 : ℝ)..1,
        -(1 /
            ((1 + weierstrass u) *
              (1 + Real.sqrt (1 - weierstrass u ^ 2)))) * weierstrassDeriv u := by
      exact integral_weierstrass _
    _ = ∫ u in (0 : ℝ)..1, 1 - 2 / (1 + u) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro u hu
      have hu_pos : 0 < u := hu.1
      have hu_lt : u < 1 := hu.2
      have hden_pos : 0 < 1 + u ^ 2 := by positivity
      have hnum_nonneg : 0 ≤ 1 - u ^ 2 := by nlinarith
      have hroot :
          Real.sqrt (1 - weierstrass u ^ 2) = (1 - u ^ 2) / (1 + u ^ 2) := by
        rw [show 1 - weierstrass u ^ 2 = ((1 - u ^ 2) / (1 + u ^ 2)) ^ 2 by
          unfold weierstrass
          field_simp [ne_of_gt hden_pos]
          ring]
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (div_nonneg hnum_nonneg hden_pos.le)]
      change
        -(1 /
            ((1 + weierstrass u) *
              (1 + Real.sqrt (1 - weierstrass u ^ 2)))) * weierstrassDeriv u =
          1 - 2 / (1 + u)
      rw [hroot]
      unfold weierstrass weierstrassDeriv
      field_simp [ne_of_gt hden_pos, ne_of_gt (by linarith : 0 < 1 + u)]
      ring
    _ = (∫ _u in (0 : ℝ)..1, (1 : ℝ)) -
        2 * ∫ u in (0 : ℝ)..1, 1 / (1 + u) := by
      have hconst : IntervalIntegrable (fun _u : ℝ => (1 : ℝ)) MeasureTheory.volume 0 1 :=
        continuousOn_const.intervalIntegrable
      have hrecip : IntervalIntegrable (fun u : ℝ => 2 / (1 + u))
          MeasureTheory.volume 0 1 := by
        apply ContinuousOn.intervalIntegrable
        exact continuousOn_const.div (continuousOn_const.add continuousOn_id) (fun u hu => by
          norm_num [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
          linarith)
      rw [intervalIntegral.integral_sub hconst hrecip]
      congr 1
      simpa only [div_eq_mul_inv, one_mul] using
        (intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
          (a := (0 : ℝ)) (b := 1) (2 : ℝ) (fun u : ℝ => 1 / (1 + u)))
    _ = 1 - 2 * ∫ t in (1 : ℝ)..2, 1 / t := by
      rw [show (∫ _u in (0 : ℝ)..1, (1 : ℝ)) = 1 by norm_num]
      congr 2
      simpa only [zero_add, one_add_one_eq_two, add_comm] using
        (intervalIntegral.integral_comp_add_right
          (f := fun x : ℝ ↦ 1 / x) (a := (0 : ℝ)) (b := 1) 1)
    _ = 1 - 2 * Real.log 2 := by
      rw [integral_one_div_of_pos (by norm_num) (by norm_num)]
      norm_num

/-- The half-power midslope curvature is `(5 - 12 * log 2) / 6`. -/
theorem J_half_eq : J_half = (5 - 12 * Real.log 2) / 6 := by
  rw [J_half]
  calc
    _ = ∫ t in (0 : ℝ)..1,
        ((1 - t) / t ^ 2) *
          (2 / (1 + Real.sqrt (1 - t ^ 2)) - 1 / (1 - t ^ 2)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      have ht_lt : t < 1 := ht.2
      have ha : 0 ≤ (1 + t) / 2 := by linarith [ht.1]
      have hb : 0 ≤ (1 - t) / 2 := by linarith
      have hsquare : 0 < 1 - t ^ 2 := by
        nlinarith [mul_pos (sub_pos.mpr ht_lt) (by linarith [ht.1] : 0 < 1 + t)]
      have hsqrt_product :
          Real.sqrt (((1 + t) / 2) * ((1 - t) / 2)) =
            Real.sqrt (1 - t ^ 2) / 2 := by
        rw [show ((1 + t) / 2) * ((1 - t) / 2) = (1 - t ^ 2) / 4 by ring]
        rw [Real.sqrt_div hsquare.le]
        have hsqrt_four : Real.sqrt (4 : ℝ) = 2 := by
          have hsquare_four := Real.sq_sqrt (show (0 : ℝ) ≤ 4 by norm_num)
          have hnonneg_four := Real.sqrt_nonneg (4 : ℝ)
          nlinarith
        rw [hsqrt_four]
      have hproduct :
          Real.sqrt ((1 + t) / 2) * Real.sqrt ((1 - t) / 2) =
            Real.sqrt (1 - t ^ 2) / 2 := by
        rw [← Real.sqrt_mul ha, hsqrt_product]
      have hsqrt_sum :
          (Real.sqrt ((1 + t) / 2) + Real.sqrt ((1 - t) / 2)) ^ 2 =
            1 + Real.sqrt (1 - t ^ 2) := by
        rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
        calc
          (1 + t) / 2 + 2 * Real.sqrt ((1 + t) / 2) * Real.sqrt ((1 - t) / 2) +
                (1 - t) / 2 =
              (1 + t) / 2 +
                2 * (Real.sqrt ((1 + t) / 2) * Real.sqrt ((1 - t) / 2)) +
                (1 - t) / 2 := by ring
          _ = 1 + Real.sqrt (1 - t ^ 2) := by rw [hproduct]; ring
      have hhalf :
          2 * meanHalf ((1 + t) / 2) ((1 - t) / 2) =
            (1 + Real.sqrt (1 - t ^ 2)) / 2 := by
        rw [meanHalf, hsqrt_sum]
        ring
      change
        (1 - t) / t ^ 2 *
            (1 / (2 * meanHalf ((1 + t) / 2) ((1 - t) / 2)) - 1 / (1 - t ^ 2)) =
          (1 - t) / t ^ 2 *
            (2 / (1 + Real.sqrt (1 - t ^ 2)) - 1 / (1 - t ^ 2))
      rw [hhalf]
      have hden_pos : 0 < 1 + Real.sqrt (1 - t ^ 2) := by positivity
      field_simp [ne_of_gt hden_pos]
    _ = ∫ u in (0 : ℝ)..1,
        (((1 - weierstrass u) / weierstrass u ^ 2) *
          (2 / (1 + Real.sqrt (1 - weierstrass u ^ 2)) -
            1 / (1 - weierstrass u ^ 2))) * weierstrassDeriv u := by
      exact integral_weierstrass _
    _ = ∫ u in (0 : ℝ)..1, -u ^ 2 / 2 + u + 1 / 2 - 2 / (1 + u) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro u hu
      have hu_pos : 0 < u := hu.1
      have hu_lt : u < 1 := hu.2
      have hden_pos : 0 < 1 + u ^ 2 := by positivity
      have hsub_pos : 0 < 1 - u ^ 2 := by nlinarith
      have hweierstrass_square :
          1 - weierstrass u ^ 2 = ((1 - u ^ 2) / (1 + u ^ 2)) ^ 2 := by
        unfold weierstrass
        field_simp [ne_of_gt hden_pos]
        ring
      have hroot :
          Real.sqrt (1 - weierstrass u ^ 2) = (1 - u ^ 2) / (1 + u ^ 2) := by
        rw [hweierstrass_square, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (div_nonneg hsub_pos.le hden_pos.le)]
      change
        ((1 - weierstrass u) / weierstrass u ^ 2 *
            (2 / (1 + Real.sqrt (1 - weierstrass u ^ 2)) -
              1 / (1 - weierstrass u ^ 2))) * weierstrassDeriv u =
          -u ^ 2 / 2 + u + 1 / 2 - 2 / (1 + u)
      rw [hroot, hweierstrass_square]
      unfold weierstrass weierstrassDeriv
      field_simp [ne_of_gt hu_pos, ne_of_gt hden_pos, ne_of_gt hsub_pos,
        ne_of_gt (by linarith : 0 < 1 + u)]
      ring
    _ = 5 / 6 - 2 * Real.log 2 := by
      have hpoly_cont :
          ContinuousOn (fun u : ℝ => -u ^ 2 / 2 + u + 1 / 2) (Set.uIcc 0 1) := by
        fun_prop
      have hrecip_cont :
          ContinuousOn (fun u : ℝ => 2 / (1 + u)) (Set.uIcc 0 1) := by
        exact continuousOn_const.div (continuousOn_const.add continuousOn_id) (fun u hu => by
          norm_num [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
          linarith)
      rw [intervalIntegral.integral_sub hpoly_cont.intervalIntegrable
        hrecip_cont.intervalIntegrable]
      have hpoly :
          (∫ u in (0 : ℝ)..1, -u ^ 2 / 2 + u + 1 / 2) = 5 / 6 := by
        have hfirst :
            IntervalIntegrable (fun u : ℝ => -u ^ 2 / 2) MeasureTheory.volume 0 1 := by
          exact (by fun_prop : Continuous fun u : ℝ => -u ^ 2 / 2).continuousOn.intervalIntegrable
        have hsecond :
            IntervalIntegrable (fun u : ℝ => u) MeasureTheory.volume 0 1 := by
          exact continuous_id.continuousOn.intervalIntegrable
        have hthird :
            IntervalIntegrable (fun _u : ℝ => (1 : ℝ) / 2) MeasureTheory.volume 0 1 := by
          exact continuous_const.continuousOn.intervalIntegrable
        rw [intervalIntegral.integral_add (hfirst.add hsecond) hthird,
          intervalIntegral.integral_add hfirst hsecond]
        norm_num [integral_pow, integral_id, intervalIntegral.integral_div,
          intervalIntegral.integral_neg]
      have hrecip : (∫ u in (0 : ℝ)..1, 2 / (1 + u)) = 2 * Real.log 2 := by
        calc
          _ = 2 * ∫ u in (0 : ℝ)..1, 1 / (1 + u) := by
            simpa only [div_eq_mul_inv, one_mul] using
              (intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
                (a := (0 : ℝ)) (b := 1) (2 : ℝ) (fun u : ℝ => 1 / (1 + u)))
          _ = 2 * ∫ t in (1 : ℝ)..2, 1 / t := by
            congr 1
            simpa only [zero_add, one_add_one_eq_two, add_comm] using
              (intervalIntegral.integral_comp_add_right
                (f := fun x : ℝ ↦ 1 / x) (a := (0 : ℝ)) (b := 1) 1)
          _ = 2 * Real.log 2 := by
            rw [integral_one_div_of_pos (by norm_num) (by norm_num)]
            norm_num
      rw [hpoly, hrecip]
    _ = (5 - 12 * Real.log 2) / 6 := by ring

/-- The half-power value is the stated affine combination of the geometric and arithmetic values. -/
theorem J_half_eq_affine : J_half = (5 / 6) * J_zero + (1 / 3) * J_one := by
  rw [J_half_eq, J_zero_eq_one_sub_two_log_two, J_one_eq_neg_log_two]
  ring

end D5.S3.Constants.MidslopeCurvatureValues
