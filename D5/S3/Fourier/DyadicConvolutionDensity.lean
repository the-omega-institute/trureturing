/- GID: D5/S3/Fourier/DyadicConvolutionDensity
   generality: I
   mirror-B: D5/B/S3/Fourier/DyadicConvolutionDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite dyadic convolution densities have the prescribed Fourier-Laplace products. -/

/- Library-search audit trail (2026-09-07):
   * D5: `dyadicConvolution`, `partial_convolution`, and `infinite convolution`
     found only InfiniteSincProduct's component densities and product theorem.
     ConvolutionPowerAmplification.fourierLaplace_convolve_complex requires
     smooth WeilTestFunction inputs, excluding uniform interval densities.
   * Pinned Mathlib v4.33.0: `integral_convolution`,
     `Integrable.integrable_convolution`, `convolution_neg_of_neg_eq`,
     `support_convolution_subset`, and
     `HasProdUniformlyOn.tendstoUniformlyOn_finsetRange` supply the general
     integration and convergence machinery. `fourier_mul_convolution_eq`
     concerns real frequencies. No `infinite convolution` declaration was
     found by textual search of Mathlib.
   * GitHub repository searches via NyxID: `Lean4 "infinite convolution"`
     returned zero; `convolution language:Lean` returned the Boolean-cube
     TalagrandConvolutionConjecture (README and tree inspected) and the finite
     Dirichlet-convolution formal-langlands-lab, neither matching this slice.
     `Lean "Fabius"` returned an unrelated agent plugin. Global code search
     for `"infinite convolution" language:Lean` returned HTTP 401;
     code-level third-party completeness is ASSUMED-UNVERIFIED.
   The finite sequence uses n+1 components: zero-fold convolution is a Dirac
   measure and has no Lebesgue density. This is only an index shift of the
   preregistered finite-convolution witness.
-/

import D5.S3.Fourier.InfiniteSincProduct
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace D5.S3.Fourier.DyadicConvolutionDensity

open Filter MeasureTheory Set Topology
open D5.S3.Fourier.InfiniteSincProduct
open scoped Convolution Pointwise

noncomputable section

/-- The positive-sign convention used by the frozen uniform factors. -/
def densityFourierLaplace (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (f x : ℂ) * Complex.exp (Complex.I * z * x)

/-- The convolution of components indexed from zero through n. -/
def dyadicPartialConvolution (ell : ℝ) : ℕ → ℝ → ℝ
  | 0 => uniformIntervalDensity (dyadicHalfWidth ell 0)
  | n + 1 => (dyadicPartialConvolution ell n) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
      uniformIntervalDensity (dyadicHalfWidth ell (n + 1))

private def tilt (f : ℝ → ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  (f x : ℂ) * Complex.exp (Complex.I * z * x)

private theorem tilt_convolution (f g : ℝ → ℝ) (z : ℂ) :
    tilt (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) z =
      (tilt f z) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (tilt g z) := by
  funext x
  simp only [tilt, convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_complex_ofReal, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with t
  push_cast
  have hexp : Complex.exp (Complex.I * z * (x : ℂ)) =
      Complex.exp (Complex.I * z * (t : ℂ)) *
        Complex.exp (Complex.I * z * ((x : ℂ) - t)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

private theorem tilt_uniform_integrable (a : ℝ) (z : ℂ) :
    Integrable (tilt (uniformIntervalDensity a) z) := by
  have heq : tilt (uniformIntervalDensity a) z =
      (Icc (-a) a).indicator
        (fun x : ℝ => ((2 * a : ℝ)⁻¹ : ℂ) * Complex.exp (Complex.I * z * x)) := by
    funext x
    by_cases hx : x ∈ Icc (-a) a <;> simp [tilt, uniformIntervalDensity, hx]
  rw [heq]
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  apply Continuous.integrableOn_Icc
  fun_prop

private theorem tilt_partial_integrable (ell : ℝ) (n : ℕ) (z : ℂ) :
    Integrable (tilt (dyadicPartialConvolution ell n) z) := by
  induction n with
  | zero => exact tilt_uniform_integrable _ _
  | succ n ih =>
      rw [dyadicPartialConvolution, tilt_convolution]
      exact ih.integrable_convolution _ (tilt_uniform_integrable _ _)

/-- The finite-convolution bridge: n+1 interval components give n+1 factors. -/
theorem dyadic_partial_convolution_fourierLaplace (ell : ℝ) (n : ℕ) (z : ℂ) :
    densityFourierLaplace (dyadicPartialConvolution ell n) z =
      ∏ j ∈ Finset.range (n + 1),
        uniformIntervalFourierLaplace (dyadicHalfWidth ell j) z := by
  induction n with
  | zero => simp [dyadicPartialConvolution, densityFourierLaplace,
      uniformIntervalFourierLaplace]
  | succ n ih =>
      change (∫ x : ℝ, tilt
        ((dyadicPartialConvolution ell n) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
          uniformIntervalDensity (dyadicHalfWidth ell (n + 1))) z x) = _
      rw [tilt_convolution, integral_convolution _ (tilt_partial_integrable ell n z)
        (tilt_uniform_integrable _ _), Finset.prod_range_succ]
      change densityFourierLaplace (dyadicPartialConvolution ell n) z *
        uniformIntervalFourierLaplace (dyadicHalfWidth ell (n + 1)) z = _
      rw [ih]

theorem dyadicPartialConvolution_integrable (ell : ℝ) (n : ℕ) :
    Integrable (dyadicPartialConvolution ell n) := by
  induction n with
  | zero => exact uniformIntervalDensity_integrable _
  | succ n ih => exact ih.integrable_convolution _ (uniformIntervalDensity_integrable _)

theorem dyadicPartialConvolution_nonneg (ell : ℝ) (hell : 0 < ell) (n : ℕ) (x : ℝ) :
    0 ≤ dyadicPartialConvolution ell n x := by
  have hp (j : ℕ) : 0 < dyadicHalfWidth ell j := by
    unfold dyadicHalfWidth
    positivity
  induction n generalizing x with
  | zero => exact uniformIntervalDensity_nonneg (hp 0) x
  | succ n ih =>
      exact integral_nonneg (fun t =>
        mul_nonneg (ih t) (uniformIntervalDensity_nonneg (hp (n + 1)) (x - t)))

theorem integral_dyadicPartialConvolution (ell : ℝ) (hell : 0 < ell) (n : ℕ) :
    ∫ x : ℝ, dyadicPartialConvolution ell n x = 1 := by
  have hp (j : ℕ) : 0 < dyadicHalfWidth ell j := by
    unfold dyadicHalfWidth
    positivity
  induction n with
  | zero => exact integral_uniformIntervalDensity (hp 0)
  | succ n ih =>
      rw [dyadicPartialConvolution, integral_convolution _
        (dyadicPartialConvolution_integrable ell n) (uniformIntervalDensity_integrable _)]
      simp [ih, integral_uniformIntervalDensity (hp (n + 1))]

theorem dyadicPartialConvolution_even (ell : ℝ) (n : ℕ) (x : ℝ) :
    dyadicPartialConvolution ell n (-x) = dyadicPartialConvolution ell n x := by
  induction n generalizing x with
  | zero => exact uniformIntervalDensity_even _ _
  | succ n ih =>
      exact convolution_neg_of_neg_eq _ (Eventually.of_forall ih)
        (Eventually.of_forall (uniformIntervalDensity_even _))

private theorem partial_support (ell : ℝ) (n : ℕ) :
    Function.support (dyadicPartialConvolution ell n) ⊆
      Icc (-(∑ j ∈ Finset.range (n + 1), dyadicHalfWidth ell j))
        (∑ j ∈ Finset.range (n + 1), dyadicHalfWidth ell j) := by
  have hs (j : ℕ) : Function.support (uniformIntervalDensity (dyadicHalfWidth ell j)) ⊆
      Icc (-(dyadicHalfWidth ell j)) (dyadicHalfWidth ell j) := by
    intro x hx
    by_contra hn
    exact hx (by simp [uniformIntervalDensity, hn])
  induction n with
  | zero => simpa [dyadicPartialConvolution] using hs 0
  | succ n ih =>
      intro x hx
      obtain ⟨u, hu, v, hv, rfl⟩ :=
        support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ) hx
      have hu' := ih hu
      have hv' := hs (n + 1) hv
      simp only [Finset.sum_range_succ] at hu' ⊢
      constructor <;> linarith [hu'.1, hu'.2, hv'.1, hv'.2]

/-- Every finite density already has the final support bound. -/
theorem dyadicPartialConvolution_tsupport (ell : ℝ) (hell : 0 < ell) (n : ℕ) :
    tsupport (dyadicPartialConvolution ell n) ⊆ Icc (-(ell / 2)) (ell / 2) := by
  have hs : Summable (dyadicHalfWidth ell) := by
    refine (summable_geometric_two' (ell / 2)).congr fun j => ?_
    simp [dyadicHalfWidth, pow_add]
    ring
  have hsum : (∑ j ∈ Finset.range (n + 1), dyadicHalfWidth ell j) ≤ ell / 2 := by
    rw [← (dyadic_uniform_convolution_product_ne_zero_off_real ell hell).2.1]
    exact hs.sum_le_tsum _ (fun j _ =>
      ((dyadic_uniform_convolution_product_ne_zero_off_real ell hell).1 j).1.le)
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hx' := partial_support ell n hx
  constructor <;> linarith [hx'.1, hx'.2]

/-- The transforms of the actual finite densities tend to the frozen sinc product.
This does not yet assert convergence of the densities themselves. -/
theorem dyadic_partial_convolution_fourierLaplace_tendsto
    (ell : ℝ) (hell : 0 < ell) (z : ℂ) :
    Tendsto (fun n => densityFourierLaplace (dyadicPartialConvolution ell n) z) atTop
      (nhds (∏' j, complexSinc ((dyadicHalfWidth ell j : ℝ) * z))) := by
  have hd := dyadic_uniform_convolution_product_ne_zero_off_real ell hell
  have hp := (hd.2.2.1 {z} (isCompact_singleton)).hasProd (mem_singleton z)
  have ht := hp.tendsto_prod_nat.comp (tendsto_add_atTop_nat 1)
  convert ht using 1
  funext n
  rw [dyadic_partial_convolution_fourierLaplace]
  exact Finset.prod_congr rfl (fun j _ => (hd.1 j).2.2.2.2.2 z)

private theorem uniform_density_bound {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |uniformIntervalDensity a x| ≤ (2 * a)⁻¹ := by
  by_cases hx : x ∈ Icc (-a) a
  · rw [uniformIntervalDensity, indicator_of_mem hx, abs_of_pos (by positivity)]
  · rw [uniformIntervalDensity, indicator_of_notMem hx, abs_zero]
    positivity

private theorem uniform_convolution_integrable {f : ℝ → ℝ} (hf : Integrable f)
    {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Integrable (fun t => f (x - t) * uniformIntervalDensity a t) :=
  (hf.comp_sub_left x).mul_bdd (uniformIntervalDensity_integrable a).aestronglyMeasurable
    (Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using uniform_density_bound ha t)

private theorem uniform_convolution_interval (f : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] uniformIntervalDensity a) x =
      (∫ t in (x - a)..(x + a), f t) * (2 * a)⁻¹ := by
  rw [convolution_def]
  have heq : (fun t => f t * uniformIntervalDensity a (x - t)) =
      (Icc (x - a) (x + a)).indicator (fun t => f t * (2 * a)⁻¹) := by
    funext t
    have hm : x - t ∈ Icc (-a) a ↔ t ∈ Icc (x - a) (x + a) := by
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    by_cases ht : t ∈ Icc (x - a) (x + a) <;>
      simp [uniformIntervalDensity, ht, hm]
  change (∫ t, f t * uniformIntervalDensity a (x - t)) = _
  rw [heq, integral_indicator measurableSet_Icc, integral_mul_const,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]

private theorem uniform_convolution_lipschitz_from_bound {f : ℝ → ℝ}
    (hf : Integrable f) {C a : ℝ} (ha : 0 < a) (hC : ∀ x, |f x| ≤ C) (x y : ℝ) :
    |(f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] uniformIntervalDensity a) x -
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] uniformIntervalDensity a) y| ≤
      (C / a) * |x - y| := by
  rw [uniform_convolution_interval f ha x, uniform_convolution_interval f ha y,
    ← sub_mul, abs_mul, abs_of_pos (by positivity : 0 < (2 * a)⁻¹),
    intervalIntegral.integral_interval_sub_interval_comm
      hf.intervalIntegrable hf.intervalIntegrable hf.intervalIntegrable]
  have hb (p q : ℝ) : |∫ t in p..q, f t| ≤ C * |q - p| := by
    simpa only [Real.norm_eq_abs] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (a := p) (b := q)
        (f := f) (fun t _ => by simpa only [Real.norm_eq_abs] using hC t))
  calc
    |(∫ t in (x - a)..(y - a), f t) - ∫ t in (x + a)..(y + a), f t| * (2 * a)⁻¹ ≤
        (C * |(y - a) - (x - a)| + C * |(y + a) - (x + a)|) * (2 * a)⁻¹ := by
      gcongr
      exact (abs_sub _ _).trans (add_le_add (hb _ _) (hb _ _))
    _ = (C / a) * |x - y| := by
      rw [show y - a - (x - a) = y - x by ring,
        show y + a - (x + a) = y - x by ring, abs_sub_comm y x]
      field_simp
      ring

private theorem uniform_convolution_lipschitz {f : ℝ → ℝ} (hf : Integrable f)
    {a L : ℝ} (ha : 0 < a) (hL : ∀ x y, |f x - f y| ≤ L * |x - y|) (x y : ℝ) :
    |(f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] uniformIntervalDensity a) x -
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] uniformIntervalDensity a) y| ≤
      L * |x - y| := by
  rw [convolution_mul_swap, convolution_mul_swap,
    ← integral_sub (uniform_convolution_integrable hf ha x)
      (uniform_convolution_integrable hf ha y)]
  have hb : ∀ t, ‖f (x - t) * uniformIntervalDensity a t -
      f (y - t) * uniformIntervalDensity a t‖ ≤
      (L * |x - y|) * uniformIntervalDensity a t := by
    intro t
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul,
      abs_of_nonneg (uniformIntervalDensity_nonneg ha t)]
    have hd : x - t - (y - t) = x - y := by ring
    exact mul_le_mul_of_nonneg_right (hd ▸ hL (x - t) (y - t))
      (uniformIntervalDensity_nonneg ha t)
  have hi := norm_integral_le_of_norm_le
    ((uniformIntervalDensity_integrable a).const_mul (L * |x - y|))
    (Eventually.of_forall hb)
  simpa [Real.norm_eq_abs, integral_const_mul, integral_uniformIntervalDensity ha] using hi

private theorem uniform_convolution_close {f : ℝ → ℝ} (hf : Integrable f)
    {a L : ℝ} (ha : 0 < a) (hL₀ : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * |x - y|) (x : ℝ) :
    |(f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] uniformIntervalDensity a) x - f x| ≤
      L * a := by
  rw [convolution_mul_swap]
  have hc : f x = ∫ t : ℝ, f x * uniformIntervalDensity a t := by
    rw [integral_const_mul, integral_uniformIntervalDensity ha, mul_one]
  rw [hc, ← integral_sub (uniform_convolution_integrable hf ha x)
    ((uniformIntervalDensity_integrable a).const_mul (f x))]
  have hb (t : ℝ) : ‖f (x - t) * uniformIntervalDensity a t -
      f x * uniformIntervalDensity a t‖ ≤ (L * a) * uniformIntervalDensity a t := by
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul,
      abs_of_nonneg (uniformIntervalDensity_nonneg ha t)]
    by_cases ht : t ∈ Icc (-a) a
    · apply mul_le_mul_of_nonneg_right _ (uniformIntervalDensity_nonneg ha t)
      have ht' : |t| ≤ a := abs_le.mpr ht
      have hd : |x - t - x| = |t| := by rw [show x - t - x = -t by ring, abs_neg]
      exact (hL (x - t) x).trans (hd ▸ mul_le_mul_of_nonneg_left ht' hL₀)
    · simp [uniformIntervalDensity, ht]
  have hi := norm_integral_le_of_norm_le
    ((uniformIntervalDensity_integrable a).const_mul (L * a)) (Eventually.of_forall hb)
  simpa [Real.norm_eq_abs, integral_const_mul, integral_uniformIntervalDensity ha] using hi

private theorem dyadic_lipschitz (ell : ℝ) (hell : 0 < ell) (n : ℕ) (x y : ℝ) :
    |dyadicPartialConvolution ell (n + 1) x - dyadicPartialConvolution ell (n + 1) y| ≤
      ((2 * dyadicHalfWidth ell 0)⁻¹ / dyadicHalfWidth ell 1) * |x - y| := by
  have hp (j : ℕ) : 0 < dyadicHalfWidth ell j := by
    unfold dyadicHalfWidth
    positivity
  induction n generalizing x y with
  | zero =>
      exact uniform_convolution_lipschitz_from_bound
        (uniformIntervalDensity_integrable _) (hp 1) (uniform_density_bound (hp 0)) x y
  | succ n ih =>
      exact uniform_convolution_lipschitz
        (dyadicPartialConvolution_integrable ell (n + 1)) (hp (n + 1 + 1)) ih x y

/-- Pointwise existence follows from summable Lipschitz displacement bounds. -/
theorem dyadicPartialConvolution_cauchy (ell : ℝ) (hell : 0 < ell) (x : ℝ) :
    CauchySeq (fun n => dyadicPartialConvolution ell (n + 1) x) := by
  let L := (2 * dyadicHalfWidth ell 0)⁻¹ / dyadicHalfWidth ell 1
  have hp (j : ℕ) : 0 < dyadicHalfWidth ell j := by
    unfold dyadicHalfWidth
    positivity
  have hL : 0 ≤ L := le_of_lt (div_pos (inv_pos.mpr (mul_pos (by norm_num) (hp 0))) (hp 1))
  apply cauchySeq_of_dist_le_of_summable (fun n => L * dyadicHalfWidth ell (n + 2))
  · intro n
    rw [Real.dist_eq, abs_sub_comm]
    exact uniform_convolution_close (dyadicPartialConvolution_integrable ell (n + 1))
      (hp (n + 2)) hL (dyadic_lipschitz ell hell n) x
  · refine (summable_geometric_two' (L * ell / 8)).congr fun n => ?_
    simp [dyadicHalfWidth, pow_add]
    ring

/-- The pointwise limit of the dyadic finite convolution densities. -/
def dyadicConvolutionDensity (ell : ℝ) (x : ℝ) : ℝ :=
  limUnder atTop (fun n => dyadicPartialConvolution ell (n + 1) x)

theorem dyadicPartialConvolution_tendsto (ell : ℝ) (hell : 0 < ell) (x : ℝ) :
    Tendsto (fun n => dyadicPartialConvolution ell (n + 1) x) atTop
      (nhds (dyadicConvolutionDensity ell x)) :=
  (dyadicPartialConvolution_cauchy ell hell x).tendsto_limUnder

#print axioms dyadic_partial_convolution_fourierLaplace
#print axioms dyadic_partial_convolution_fourierLaplace_tendsto

end

end D5.S3.Fourier.DyadicConvolutionDensity
