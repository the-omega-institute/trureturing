/- GID: D5/S3/Fourier/DyadicComplexDecay
   generality: I
   mirror-B: D5/B/S3/Fourier/DyadicComplexDecay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The dyadic density transform has explicit inverse-power decay on every complex strip. -/

import D5.S3.Fourier.DyadicConvolutionDensity

namespace D5.S3.Fourier.DyadicComplexDecay

open Filter MeasureTheory Set Topology
open D5.S3.Fourier.InfiniteSincProduct
open D5.S3.Fourier.DyadicConvolutionDensity

noncomputable section

/-- An arbitrary prefix gives an explicit decay constant; the total half-width
controls growth in the imaginary direction. -/
theorem dyadic_transform_explicit_strip_decay (ell : ℝ) (hell : 0 < ell)
    (k : ℕ) (z : ℂ) :
    ‖densityFourierLaplace (dyadicConvolutionDensity ell) z‖ ≤
      Real.exp (ell * |z.im| / 2) *
        (∏ j ∈ Finset.range k, (1 + (dyadicHalfWidth ell j)⁻¹)) / (1 + ‖z‖) ^ k := by
  have hd := dyadic_uniform_convolution_product_ne_zero_off_real ell hell
  have ha (j : ℕ) : 0 < dyadicHalfWidth ell j := (hd.1 j).1
  have hstrip (a : ℝ) (ha : 0 < a) :
      ‖complexSinc ((a : ℂ) * z)‖ ≤ Real.exp (a * |z.im|) := by
    rw [← uniformIntervalFourierLaplace_eq_complexSinc ha, uniformIntervalFourierLaplace]
    calc
      ‖∫ x : ℝ, (uniformIntervalDensity a x : ℂ) *
          Complex.exp (Complex.I * z * x)‖ ≤
          ∫ x : ℝ, Real.exp (a * |z.im|) * uniformIntervalDensity a x := by
        apply norm_integral_le_of_norm_le
          ((uniformIntervalDensity_integrable a).const_mul _)
        filter_upwards [] with x
        by_cases hx : x ∈ Icc (-a) a
        · have hxabs : |x| ≤ a := abs_le.mpr hx
          have he : (Complex.I * z * (x : ℂ)).re ≤ a * |z.im| := by
            simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
              Complex.ofReal_im, zero_mul, mul_zero, one_mul, sub_zero, zero_sub]
            calc
              -z.im * x ≤ |z.im| * |x| := by
                simpa [abs_mul] using le_abs_self (-z.im * x)
              _ ≤ a * |z.im| := by nlinarith [abs_nonneg z.im]
          rw [norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (uniformIntervalDensity_nonneg ha x), Complex.norm_exp]
          simpa [mul_comm] using mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
            (uniformIntervalDensity_nonneg ha x)
        · simp [uniformIntervalDensity, hx]
      _ = Real.exp (a * |z.im|) := by
        rw [integral_const_mul, integral_uniformIntervalDensity ha, mul_one]
  have hsin (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
    have hp : ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp |w.im| := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simpa using neg_le_abs w.im
    have hn : ‖Complex.exp (-(w * Complex.I))‖ ≤ Real.exp |w.im| := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simpa using le_abs_self w.im
    have hden : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one, hden]
    rw [neg_mul]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      ((norm_sub_le _ _).trans (by linarith))
  have hinv (a : ℝ) (ha : 0 < a) :
      ‖complexSinc ((a : ℂ) * z)‖ * ‖z‖ ≤ Real.exp (a * |z.im|) * a⁻¹ := by
    by_cases hz : z = 0
    · simp [hz, ha.le]
    · have hw : (a : ℂ) * z ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne') hz
      rw [complexSinc_of_ne_zero hw, norm_div, norm_mul, Complex.norm_of_nonneg ha.le]
      have hs := hsin ((a : ℂ) * z)
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        add_zero, abs_mul, abs_of_pos ha] at hs
      calc
        ‖Complex.sin ((a : ℂ) * z)‖ / (a * ‖z‖) * ‖z‖ =
            ‖Complex.sin ((a : ℂ) * z)‖ * a⁻¹ := by
          field_simp [ha.ne', norm_ne_zero_iff.mpr hz]
        _ ≤ Real.exp (a * |z.im|) * a⁻¹ :=
          mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr ha.le)
  let b : ℕ → ℝ := fun j =>
    ‖complexSinc ((dyadicHalfWidth ell j : ℝ) * z)‖ /
      Real.exp (dyadicHalfWidth ell j * |z.im|)
  have hb0 (j : ℕ) : 0 ≤ b j := by dsimp [b]; positivity
  have hb1 (j : ℕ) : b j ≤ 1 := by
    exact (div_le_one (Real.exp_pos _)).mpr (hstrip _ (ha j))
  have hbk (j : ℕ) : b j ≤ (1 + (dyadicHalfWidth ell j)⁻¹) / (1 + ‖z‖) := by
    dsimp [b]
    apply (div_le_div_iff₀ (Real.exp_pos _) (by positivity)).mpr
    have h₁ := hstrip _ (ha j)
    have h₂ := hinv _ (ha j)
    nlinarith
  have hsum : Summable (dyadicHalfWidth ell) := by
    have hg : Summable (fun n : ℕ => ((1 : ℝ) / 2) ^ n) :=
      summable_geometric_of_norm_lt_one (by norm_num)
    refine (hg.mul_left (ell / 4)).congr fun n => ?_
    simp [dyadicHalfWidth, pow_add]
    ring
  have hwidth (n : ℕ) : (∑ j ∈ Finset.range n, dyadicHalfWidth ell j) ≤ ell / 2 := by
    rw [← hd.2.1]
    exact hsum.sum_le_tsum _ (fun j _ => (ha j).le)
  have hprefix (n : ℕ) (hn : k ≤ n) :
      ‖∏ j ∈ Finset.range n, complexSinc ((dyadicHalfWidth ell j : ℝ) * z)‖ ≤
        Real.exp (ell * |z.im| / 2) *
          (∏ j ∈ Finset.range k, (1 + (dyadicHalfWidth ell j)⁻¹)) / (1 + ‖z‖) ^ k := by
    have hb : (∏ j ∈ Finset.range n, b j) ≤
        (∏ j ∈ Finset.range k, (1 + (dyadicHalfWidth ell j)⁻¹)) / (1 + ‖z‖) ^ k := by
      calc
        _ ≤ ∏ j ∈ Finset.range k, b j :=
          Finset.prod_le_prod_of_subset_of_le_one (Finset.range_mono hn)
            (fun j _ => hb0 j) (fun j _ _ => hb1 j)
        _ ≤ ∏ j ∈ Finset.range k, (1 + (dyadicHalfWidth ell j)⁻¹) / (1 + ‖z‖) :=
          Finset.prod_le_prod (fun j _ => hb0 j) (fun j _ => hbk j)
        _ = _ := by simp [Finset.prod_div_distrib]
    have he : Real.exp ((∑ j ∈ Finset.range n, dyadicHalfWidth ell j) * |z.im|) ≤
        Real.exp (ell * |z.im| / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hwidth n, abs_nonneg z.im]
    calc
      _ = Real.exp ((∑ j ∈ Finset.range n, dyadicHalfWidth ell j) * |z.im|) *
          ∏ j ∈ Finset.range n, b j := by
        simp only [b, Finset.prod_div_distrib, ← Real.exp_sum, ← Finset.sum_mul, norm_prod]
        rw [mul_div_cancel₀ _ (Real.exp_ne_zero _)]
      _ ≤ Real.exp (ell * |z.im| / 2) *
          ((∏ j ∈ Finset.range k, (1 + (dyadicHalfWidth ell j)⁻¹)) / (1 + ‖z‖) ^ k) :=
        mul_le_mul he hb (Finset.prod_nonneg fun j _ => hb0 j) (Real.exp_pos _).le
      _ = _ := by ring
  rw [dyadicConvolutionDensity_fourierLaplace ell hell]
  apply le_of_tendsto ((hd.2.2.1 {z} isCompact_singleton).hasProd
    (mem_singleton z)).tendsto_prod_nat.norm
  filter_upwards [eventually_ge_atTop k] with n hn
  exact hprefix n hn

#print axioms dyadic_transform_explicit_strip_decay

end

end D5.S3.Fourier.DyadicComplexDecay
