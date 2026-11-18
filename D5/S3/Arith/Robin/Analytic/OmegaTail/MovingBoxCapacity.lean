/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/MovingBoxCapacity
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/MovingBoxCapacity
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Finite local Abel error and capacity of shrinking logarithmic prime boxes. -/

import D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
import D5.S3.Arith.Robin.PriceRecord.UniformThetaShellError

/-! Local Abel summation on real-endpoint prime boxes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.Analytic.OmegaTail.MovingBoxCapacity
open Real Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel (primeInterval primeCount
  theta_error_log_power)
open D5.S3.Arith.Robin.PriceRecord.UniformThetaShellError

private lemma continuousOn_inv_log {y z : ℝ} (hy : 1 < y) :
    ContinuousOn (fun t : ℝ => (log t)⁻¹) (Icc y z) := by
  intro t ht
  have ht1 := hy.trans_le ht.1
  exact (continuousAt_log (by linarith : t ≠ 0)).inv₀ (log_pos ht1).ne'
    |>.continuousWithinAt

/-- The local prime count differs from its logarithmic integral by at most
twice the uniform theta error divided by the logarithm of the lower endpoint. -/
theorem abs_primeInterval_card_sub_integral_le {y z E : ℝ}
    (hy : 2 ≤ y) (hyz : y ≤ z)
    (hE : ∀ t ∈ Icc y z, |Chebyshev.theta t - t| ≤ E) :
    |((primeInterval y z).card : ℝ) - ∫ t in y..z, (log t)⁻¹| ≤ 2 * E / log y := by
  let k : ℝ → ℝ := fun t => (t * log t ^ 2)⁻¹
  let e : ℝ → ℝ := fun t => Chebyshev.theta t - t
  have ht (t : ℝ) (h : t ∈ Icc y z) : 1 < t := by linarith [h.1]
  have hk0 (t : ℝ) (h : t ∈ Icc y z) : 0 ≤ k t := by
    dsimp [k]
    exact inv_nonneg.mpr (mul_nonneg (by linarith [ht t h]) (sq_nonneg _))
  have hkc : ContinuousOn k (Icc y z) := by
    intro t h
    have h0 : t ≠ 0 := by linarith [ht t h]
    have hl := (log_pos (ht t h)).ne'
    exact ((continuousAt_id.mul ((continuousAt_log h0).pow 2)).inv₀
      (mul_ne_zero h0 (pow_ne_zero 2 hl))).continuousWithinAt
  have hki := hkc.intervalIntegrable_of_Icc (μ := volume) hyz
  have hti : IntervalIntegrable (fun t => t * k t) volume y z :=
    (continuousOn_id.mul hkc).intervalIntegrable_of_Icc (μ := volume) hyz
  have hθ (x : ℝ) (hx : 2 ≤ x) :
      IntervalIntegrable (fun t => Chebyshev.theta t * k t) volume 2 x := by
    simpa only [k, div_eq_mul_inv] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
        (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have hθlocal := (hθ y hy).symm.trans (hθ z (hy.trans hyz))
  have hinv := (continuousOn_inv_log (by linarith : 1 < y)).intervalIntegrable_of_Icc
    (μ := volume) hyz
  have hei : IntervalIntegrable (fun t => e t * k t) volume y z := by
    simpa only [e, sub_mul] using hθlocal.sub hti
  have hder (t : ℝ) (h : t ∈ uIcc y z) :
      HasDerivAt (fun x : ℝ => (log x)⁻¹) (-k t) t := by
    rw [uIcc_of_le hyz] at h
    have h0 : t ≠ 0 := by linarith [ht t h]
    have hl := (log_pos (ht t h)).ne'
    convert (hasDerivAt_log h0).inv hl using 1
    dsimp [k]
    field_simp
  have hkernel : (∫ t in y..z, k t) = (log y)⁻¹ - (log z)⁻¹ := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hki.neg
    rw [intervalIntegral.integral_neg] at h
    linarith
  have hproduct : (∫ t in y..z, ((log t)⁻¹ - t * k t)) =
      z * (log z)⁻¹ - y * (log y)⁻¹ := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hinv.sub hti)
    intro t h
    convert (hasDerivAt_id t).mul (hder t h) using 1
    · rfl
    · simp only [id_eq, one_mul]
      ring
  have hcount : ((primeInterval y z).card : ℝ) =
      Chebyshev.theta z * (log z)⁻¹ - Chebyshev.theta y * (log y)⁻¹ +
        ∫ t in y..z, Chebyshev.theta t * k t := by
    rw [Selection.primeInterval_card hyz]
    unfold primeCount
    rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hy,
      Chebyshev.primeCounting_eq_theta_div_log_add_integral (hy.trans hyz)]
    simp only [div_eq_mul_inv, k]
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hθ y hy) hθlocal
    dsimp only [k] at hadd
    linarith only [hadd]
  have herror : ((primeInterval y z).card : ℝ) - (∫ t in y..z, (log t)⁻¹) =
      e z * (log z)⁻¹ - e y * (log y)⁻¹ + ∫ t in y..z, e t * k t := by
    rw [hcount]
    simp only [e, sub_mul]
    rw [intervalIntegral.integral_sub hθlocal hti,
      intervalIntegral.integral_sub hinv hti] at *
    linarith only [hproduct]
  have habs : |∫ t in y..z, e t * k t| ≤ E * ((log y)⁻¹ - (log z)⁻¹) := by
    rw [← hkernel, ← intervalIntegral.integral_const_mul]
    apply (intervalIntegral.abs_integral_le_integral_abs hyz).trans
    apply intervalIntegral.integral_mono_on hyz (by simpa only [Real.norm_eq_abs] using hei.norm)
      (hki.const_mul E)
    intro t h
    rw [abs_mul, abs_of_nonneg (hk0 t h)]
    exact mul_le_mul_of_nonneg_right (hE t h) (hk0 t h)
  have hylog : 0 ≤ (log y)⁻¹ := inv_nonneg.mpr (log_pos (ht y ⟨le_rfl, hyz⟩)).le
  have hzlog : 0 ≤ (log z)⁻¹ := inv_nonneg.mpr (log_pos (ht z ⟨hyz, le_rfl⟩)).le
  rw [herror]
  calc
    _ ≤ |e z * (log z)⁻¹ - e y * (log y)⁻¹| + |∫ t in y..z, e t * k t| :=
      abs_add_le _ _
    _ ≤ |e z| * (log z)⁻¹ + |e y| * (log y)⁻¹ +
        E * ((log y)⁻¹ - (log z)⁻¹) := by
      apply add_le_add _ habs
      simpa only [abs_mul, abs_of_nonneg hylog, abs_of_nonneg hzlog, abs_neg, sub_eq_add_neg]
        using (abs_add_le (e z * (log z)⁻¹) (-(e y * (log y)⁻¹)))
    _ ≤ E * (log z)⁻¹ + E * (log y)⁻¹ + E * ((log y)⁻¹ - (log z)⁻¹) :=
      add_le_add_left (add_le_add
        (mul_le_mul_of_nonneg_right (hE z ⟨hyz, le_rfl⟩) hzlog)
        (mul_le_mul_of_nonneg_right (hE y ⟨le_rfl, hyz⟩) hylog)) _
    _ = _ := by rw [div_eq_mul_inv]; ring

end D5.S3.Arith.Robin.Analytic.OmegaTail.MovingBoxCapacity
