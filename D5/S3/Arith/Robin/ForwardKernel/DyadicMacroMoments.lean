/- GID: D5/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logarithmic dyadic power moments have explicit values and strict mixed covariance. -/

import D5.S3.Arith.Robin.ForwardKernel.DyadicProbability

/-! Power moments of the common macroscopic dyadic scale. -/

namespace D5.S3.Arith.Robin.ForwardKernel.DyadicMacroMoments

open Set MeasureTheory
open DyadicProbability

noncomputable section
set_option autoImplicit false

/-- The power moment of the logarithmic probability measure on `[1,2]`. -/
def dyadicMacroMoment (γ : ℝ) : ℝ :=
  ∫ u, u ^ γ ∂dyadicProbabilityMeasure 1

private def macroIntegral (γ : ℝ) : ℝ :=
  ∫ u in (1 : ℝ)..2, u ^ γ / u

private lemma power_continuous (γ : ℝ) :
    ContinuousOn (fun u : ℝ => u ^ γ) (Icc 1 2) := by
  apply continuousOn_id.rpow_const
  intro u hu
  exact Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num) hu.1))

private lemma weight_continuous (γ : ℝ) :
    ContinuousOn (fun u : ℝ => u ^ γ / u) (Icc 1 2) := by
  exact (power_continuous γ).div continuousOn_id
    (fun u hu => ne_of_gt (lt_of_lt_of_le (by norm_num) hu.1))

private lemma weight_integrable (γ : ℝ) :
    IntervalIntegrable (fun u : ℝ => u ^ γ / u) volume 1 2 := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using weight_continuous γ

private lemma reciprocal_integrable :
    IntervalIntegrable (fun u : ℝ => 1 / u) volume 1 2 := by
  simp

private lemma reciprocal_integral :
    (∫ u in (1 : ℝ)..2, 1 / u) = Real.log 2 := by
  simp

private lemma moment_eq_integral (γ : ℝ) :
    dyadicMacroMoment γ = macroIntegral γ / Real.log 2 := by
  simpa [dyadicMacroMoment, macroIntegral] using
    dyadicProbabilityMeasure_integral (by norm_num : (0 : ℝ) < 1) (fun u => u ^ γ)

/-- Positive power moments have the explicit logarithmic quotient. -/
theorem dyadic_macro_moment_eq {γ : ℝ} (hγ : 0 < γ) :
    dyadicMacroMoment γ = (2 ^ γ - 1) / (γ * Real.log 2) := by
  rw [moment_eq_integral, macroIntegral]
  have he : (∫ u in (1 : ℝ)..2, u ^ γ / u) =
      ∫ u in (1 : ℝ)..2, u ^ (γ - 1) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : 0 < u := by
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hu
      linarith [hu.1]
    dsimp only
    rw [Real.rpow_sub hu0, Real.rpow_one]
  rw [he, integral_rpow (Or.inl (by linarith : (-1 : ℝ) < γ - 1))]
  simp only [sub_add_cancel, Real.one_rpow, div_div]

/-- Every positive power has a strictly positive dyadic moment. -/
theorem dyadic_macro_moment_pos {γ : ℝ} (hγ : 0 < γ) :
    0 < dyadicMacroMoment γ := by
  rw [dyadic_macro_moment_eq hγ]
  apply div_pos
  · exact sub_pos.mpr (by
      simpa using Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (1 : ℝ) < 2) hγ)
  · exact mul_pos hγ (Real.log_pos (by norm_num))

private lemma difference_nonneg {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : u ∈ Icc (1 : ℝ) 2) (hv : v ∈ Icc (1 : ℝ) 2) :
    0 ≤ (u ^ a - v ^ a) * (u ^ b - v ^ b) / v := by
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hv0 : 0 ≤ v := by linarith [hv.1]
  apply div_nonneg _ hv0
  rcases le_total v u with h | h
  · exact mul_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hv0 h ha.le))
      (sub_nonneg.mpr (Real.rpow_le_rpow hv0 h hb.le))
  · exact mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr (Real.rpow_le_rpow hu0 h ha.le))
      (sub_nonpos.mpr (Real.rpow_le_rpow hu0 h hb.le))

private lemma difference_continuous (a b u : ℝ) :
    ContinuousOn (fun v : ℝ => (u ^ a - v ^ a) * (u ^ b - v ^ b) / v)
      (Icc 1 2) := by
  exact ((continuousOn_const.sub (power_continuous a)).mul
    (continuousOn_const.sub (power_continuous b))).div continuousOn_id
      (fun v hv => ne_of_gt (lt_of_lt_of_le (by norm_num) hv.1))

private lemma difference_integral (a b u : ℝ) :
    (∫ v in (1 : ℝ)..2, (u ^ a - v ^ a) * (u ^ b - v ^ b) / v) =
      u ^ a * u ^ b * Real.log 2 - u ^ a * macroIntegral b -
        u ^ b * macroIntegral a + macroIntegral (a + b) := by
  have he : (∫ v in (1 : ℝ)..2, (u ^ a - v ^ a) * (u ^ b - v ^ b) / v) =
      ∫ v in (1 : ℝ)..2,
        ((u ^ a * u ^ b) * (1 / v) - u ^ a * (v ^ b / v) -
          u ^ b * (v ^ a / v) + v ^ (a + b) / v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv0 : 0 < v := by
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hv
      linarith [hv.1]
    dsimp only
    rw [Real.rpow_add hv0]
    ring
  rw [he, intervalIntegral.integral_add
    (((reciprocal_integrable.const_mul _).sub ((weight_integrable b).const_mul _)).sub
      ((weight_integrable a).const_mul _)) (weight_integrable (a + b)),
    intervalIntegral.integral_sub
      ((reciprocal_integrable.const_mul _).sub ((weight_integrable b).const_mul _))
      ((weight_integrable a).const_mul _),
    intervalIntegral.integral_sub (reciprocal_integrable.const_mul _)
      ((weight_integrable b).const_mul _)]
  simp only [intervalIntegral.integral_const_mul, reciprocal_integral, macroIntegral]

private lemma covariance_integral_identity (a b : ℝ) :
    (∫ u in (1 : ℝ)..2,
      (∫ v in (1 : ℝ)..2, (u ^ a - v ^ a) * (u ^ b - v ^ b) / v) / u) =
      2 * (Real.log 2 * macroIntegral (a + b) - macroIntegral a * macroIntegral b) := by
  have he : (∫ u in (1 : ℝ)..2,
      (∫ v in (1 : ℝ)..2, (u ^ a - v ^ a) * (u ^ b - v ^ b) / v) / u) =
      ∫ u in (1 : ℝ)..2,
        (Real.log 2 * (u ^ (a + b) / u) - macroIntegral b * (u ^ a / u) -
          macroIntegral a * (u ^ b / u) + macroIntegral (a + b) * (1 / u)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : 0 < u := by
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hu
      linarith [hu.1]
    dsimp only
    rw [difference_integral, Real.rpow_add hu0]
    ring
  rw [he, intervalIntegral.integral_add
    ((((weight_integrable (a + b)).const_mul _).sub
      ((weight_integrable a).const_mul _)).sub ((weight_integrable b).const_mul _))
    (reciprocal_integrable.const_mul _),
    intervalIntegral.integral_sub
      (((weight_integrable (a + b)).const_mul _).sub ((weight_integrable a).const_mul _))
      ((weight_integrable b).const_mul _),
    intervalIntegral.integral_sub ((weight_integrable (a + b)).const_mul _)
      ((weight_integrable a).const_mul _)]
  simp only [intervalIntegral.integral_const_mul, reciprocal_integral, macroIntegral]
  ring

/-- Two positive powers of the shared dyadic scale have strictly positive covariance. -/
theorem dyadic_macro_moment_strict_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    dyadicMacroMoment a * dyadicMacroMoment b < dyadicMacroMoment (a + b) := by
  let J : ℝ → ℝ := fun u =>
    ∫ v in (1 : ℝ)..2, (u ^ a - v ^ a) * (u ^ b - v ^ b) / v
  have hJnonneg (u : ℝ) (hu : u ∈ Icc (1 : ℝ) 2) : 0 ≤ J u := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro v hv
    exact difference_nonneg ha hb hu hv
  have hJpos : 0 < J 2 := by
    apply intervalIntegral.integral_pos (by norm_num) (difference_continuous a b 2)
    · intro v hv
      exact difference_nonneg ha hb (by norm_num) ⟨hv.1.le, hv.2⟩
    · refine ⟨1, by norm_num, ?_⟩
      simp only [Real.one_rpow, div_one]
      exact mul_pos
        (sub_pos.mpr (by simpa using (Real.rpow_lt_rpow
          (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2) ha)))
        (sub_pos.mpr (by simpa using (Real.rpow_lt_rpow
          (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2) hb)))
  have hJcont : ContinuousOn J (Icc (1 : ℝ) 2) := by
    have he : J = fun u => u ^ a * u ^ b * Real.log 2 - u ^ a * macroIntegral b -
        u ^ b * macroIntegral a + macroIntegral (a + b) := by
      funext u
      exact difference_integral a b u
    rw [he]
    exact ((((power_continuous a).mul (power_continuous b)).mul continuousOn_const).sub
      ((power_continuous a).mul continuousOn_const)).sub
        ((power_continuous b).mul continuousOn_const) |>.add continuousOn_const
  have hpos : 0 < ∫ u in (1 : ℝ)..2, J u / u := by
    apply intervalIntegral.integral_pos (by norm_num)
      (hJcont.div continuousOn_id
        (fun u hu => ne_of_gt (lt_of_lt_of_le (by norm_num) hu.1)))
    · intro u hu
      exact div_nonneg (hJnonneg u ⟨hu.1.le, hu.2⟩) (zero_lt_one.trans hu.1).le
    · exact ⟨2, by norm_num, div_pos hJpos (by norm_num)⟩
  change 0 < ∫ u in (1 : ℝ)..2,
    (∫ v in (1 : ℝ)..2, (u ^ a - v ^ a) * (u ^ b - v ^ b) / v) / u at hpos
  rw [covariance_integral_identity] at hpos
  have hcov : macroIntegral a * macroIntegral b < Real.log 2 * macroIntegral (a + b) :=
    by linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [moment_eq_integral, moment_eq_integral, moment_eq_integral, div_mul_div_comm]
  apply (div_lt_iff₀ (mul_pos hlog hlog)).mpr
  calc
    macroIntegral a * macroIntegral b < Real.log 2 * macroIntegral (a + b) := hcov
    _ = macroIntegral (a + b) / Real.log 2 * (Real.log 2 * Real.log 2) := by
      field_simp

end
end D5.S3.Arith.Robin.ForwardKernel.DyadicMacroMoments
