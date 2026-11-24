import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! A single Fourier coefficient forces recurring signed excursions of a
finite real exponential sum without computing its mean square. -/

noncomputable section

open MeasureTheory Set

namespace FiniteSpectralOscillation

def wave (w t : ℝ) : ℂ := Complex.exp ((Complex.I * (w : ℂ)) * (t : ℂ))

theorem wave_norm (w t : ℝ) : ‖wave w t‖ = 1 := by
  simp [wave, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private theorem wave_add (w v t : ℝ) : wave (w + v) t = wave w t * wave v t := by
  unfold wave
  push_cast
  rw [mul_add, add_mul, Complex.exp_add]

private theorem wave_integral_bound {w : ℝ} (hw : w ≠ 0) (a b : ℝ) :
    ‖∫ t in a..b, wave w t‖ ≤ 2 / |w| := by
  have hw' : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
  unfold wave
  rw [integral_exp_mul_complex (mul_ne_zero Complex.I_ne_zero hw'), norm_div,
    norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  exact (norm_sub_le _ _).trans (by
    change ‖wave w b‖ + ‖wave w a‖ ≤ 2
    rw [wave_norm, wave_norm]
    norm_num)

def series {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ j ∈ s, c j * wave (f j) t

private theorem continuous_wave (w : ℝ) : Continuous (wave w) := by
  unfold wave
  fun_prop

private theorem continuous_series {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → ℝ) :
    Continuous (series s c f) :=
  continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_wave (f j))

private theorem integral_series {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → ℝ) (a b : ℝ) :
    (∫ t in a..b, series s c f t) = ∑ j ∈ s, c j * ∫ t in a..b, wave (f j) t := by
  unfold series
  have h (j : ι) (_ : j ∈ s) : IntervalIntegrable
      (fun t => c j * wave (f j) t) volume a b :=
    (continuous_const.mul (continuous_wave (f j))).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum h]
  simp_rw [intervalIntegral.integral_const_mul]

private theorem integral_series_bound {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → ℝ)
    (hf : ∀ j ∈ s, f j ≠ 0) (a b : ℝ) :
    ‖∫ t in a..b, series s c f t‖ ≤ ∑ j ∈ s, ‖c j‖ * (2 / |f j|) := by
  rw [integral_series]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (wave_integral_bound (hf j hj) a b) (norm_nonneg _)

private theorem exists_negative {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (f : ι → ℝ) (hf : ∀ j ∈ s, f j ≠ 0)
    (hinj : Set.InjOn f (↑s : Set ι)) (hreal : ∀ t, (series s c f t).im = 0)
    {i : ι} (hi : i ∈ s) (hc : c i ≠ 0) :
    ∃ L : ℝ, 0 < L ∧ ∀ a : ℝ, ∃ t ∈ Icc a (a + L),
      (series s c f t).re < -(‖c i‖ / 4) := by
  classical
  let q := series s c f
  let f' (j : ι) := f j - f i
  let M := ∑ j ∈ s, ‖c j‖ * (2 / |f j|)
  let N := ∑ j ∈ s.erase i, ‖c j‖ * (2 / |f' j|)
  have hci : 0 < ‖c i‖ := norm_pos_iff.mpr hc
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => by positivity
  have hN : 0 ≤ N := Finset.sum_nonneg fun _ _ => by positivity
  let L := 2 * (M + N + 1) / ‖c i‖
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, fun a => ?_⟩
  let b := a + L
  have hab : a ≤ b := by dsimp [b]; linarith
  by_contra! h
  have hqcont : Continuous q := continuous_series s c f
  have hqint : IntervalIntegrable q volume a b := hqcont.intervalIntegrable a b
  have hmean : (∫ t in a..b, (q t).re) ≤ M := by
    have h' : ((∫ t in a..b, q t)).re = ∫ t in a..b, (q t).re := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
      exact (integral_re hqint.1).symm
    rw [← h']
    exact (Complex.re_le_norm _).trans (integral_series_bound s c f hf a b)
  have hqreal (t : ℝ) : ‖q t‖ = |(q t).re| := by
    have he : ((q t).re : ℂ) = q t :=
      Complex.ext (Complex.ofReal_re _) (by simpa only [Complex.ofReal_im] using (hreal t).symm)
    rw [← he, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  have hupper : ‖∫ t in a..b, q t * wave (-f i) t‖ ≤ M + ‖c i‖ / 2 * L := by
    have hf' : Continuous (fun t => (q t).re + ‖c i‖ / 2) :=
      (Complex.continuous_re.comp hqcont).add continuous_const
    have hmajor : ∀ t ∈ Icc a b, ‖q t * wave (-f i) t‖ ≤ (q t).re + ‖c i‖ / 2 := by
      intro t ht
      rw [norm_mul, wave_norm, mul_one, hqreal]
      exact abs_le.mpr ⟨by linarith [h t ht], by linarith⟩
    calc
      _ ≤ ∫ t in a..b, ‖q t * wave (-f i) t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ t in a..b, (q t).re + ‖c i‖ / 2 :=
        intervalIntegral.integral_mono_on hab
          ((hqcont.mul (continuous_wave (-f i))).norm.intervalIntegrable a b)
          (hf'.intervalIntegrable a b) hmajor
      _ ≤ _ := by
        have hrealInt : IntervalIntegrable (fun t => (q t).re) volume a b :=
          (Complex.continuous_re.comp hqcont).intervalIntegrable a b
        have hconst : IntervalIntegrable (fun _ : ℝ => ‖c i‖ / 2) volume a b :=
          intervalIntegrable_const
        rw [intervalIntegral.integral_add hrealInt hconst, intervalIntegral.integral_const,
          smul_eq_mul]
        have hb : b - a = L := by dsimp [b]; ring
        rw [hb]
        linarith only [hmean]
  have hprod : ∀ t, q t * wave (-f i) t = series s c f' t := by
    intro t
    unfold q series
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_assoc, ← wave_add]
    simp only [f', sub_eq_add_neg]
  have hcorr : (∫ t in a..b, q t * wave (-f i) t) =
      c i * (L : ℂ) + ∫ t in a..b, series (s.erase i) c f' t := by
    simp_rw [hprod]
    rw [integral_series s, integral_series (s.erase i)]
    rw [← Finset.sum_erase_add _ _ hi, add_comm]
    congr 2
    have hzero : ∀ t : ℝ, wave (f' i) t = 1 := by
      intro t
      simp [f', wave]
    simp_rw [hzero]
    rw [intervalIntegral.integral_const, Complex.real_smul, mul_one,
      show b - a = L by dsimp [b]; ring]
  have herr : ‖∫ t in a..b, series (s.erase i) c f' t‖ ≤ N := by
    apply integral_series_bound
    intro j hj
    exact sub_ne_zero.mpr fun he => (Finset.mem_erase.mp hj).1
      (hinj (Finset.mem_erase.mp hj).2 hi he)
  have hlow : ‖c i‖ * L ≤ ‖∫ t in a..b, q t * wave (-f i) t‖ + N := by
    rw [hcorr]
    have he := norm_sub_le
      (c i * (L : ℂ) + ∫ t in a..b, series (s.erase i) c f' t)
      (∫ t in a..b, series (s.erase i) c f' t)
    rw [add_sub_cancel_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hL] at he
    linarith only [he, herr]
  have he : ‖c i‖ * L = 2 * (M + N + 1) := by dsimp [L]; field_simp
  linarith only [hupper, hlow, he]

/-- Every window of some fixed length contains both signs with amplitude bounded away
from zero. The length and amplitude depend only on the frequencies and coefficients. -/
theorem signed_excursions {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (f : ι → ℝ) (hf : ∀ j ∈ s, f j ≠ 0)
    (hinj : Set.InjOn f (↑s : Set ι)) (hreal : ∀ t, (series s c f t).im = 0)
    {i : ι} (hi : i ∈ s) (hc : c i ≠ 0) :
    ∃ L : ℝ, 0 < L ∧ ∀ a : ℝ,
      (∃ t ∈ Icc a (a + L), (series s c f t).re < -(‖c i‖ / 4)) ∧
      (∃ t ∈ Icc a (a + L), ‖c i‖ / 4 < (series s c f t).re) := by
  obtain ⟨L₁, hL₁, hneg⟩ := exists_negative s c f hf hinj hreal hi hc
  have hn (t : ℝ) : series s (fun j => -c j) f t = -series s c f t := by
    simp only [series, neg_mul, Finset.sum_neg_distrib]
  obtain ⟨L₂, hL₂, hpos⟩ := exists_negative s (fun j => -c j) f hf hinj
    (fun t => by rw [hn, Complex.neg_im, hreal, neg_zero]) hi (neg_ne_zero.mpr hc)
  refine ⟨max L₁ L₂, hL₁.trans_le (le_max_left _ _), fun a => ?_⟩
  obtain ⟨t₁, ht₁, h₁⟩ := hneg a
  obtain ⟨t₂, ht₂, h₂⟩ := hpos a
  rw [hn, Complex.neg_re, norm_neg, neg_lt_neg_iff] at h₂
  exact ⟨⟨t₁, ⟨ht₁.1, ht₁.2.trans (add_le_add_right (le_max_left _ _) _)⟩, h₁⟩,
    ⟨t₂, ⟨ht₂.1, ht₂.2.trans (add_le_add_right (le_max_right _ _) _)⟩, h₂⟩⟩

end FiniteSpectralOscillation

#print axioms FiniteSpectralOscillation.signed_excursions
