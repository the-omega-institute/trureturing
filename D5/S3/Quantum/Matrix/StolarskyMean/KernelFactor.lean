/- GID: D5/S3/Quantum/Matrix/StolarskyMean/KernelFactor
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/StolarskyMean/KernelFactor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive definite factors of the Stolarsky curvature kernel. -/

import D5.S3.Analytic.Fourier.PositiveDefinite.LevyDensity
import D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference
import D5.S3.Analytic.Fourier.SinhLogIntegral
import D5.S3.Quantum.Matrix.StolarskyMean.Reduction

/-! Nonnegative logarithmic densities and the quadratic deficit factor. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
open D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion
open D5.S3.Analytic.Fourier
open D5.S3.Analytic.Fourier.PositiveDefinite

namespace D5.S3.Quantum.Matrix.StolarskyMean.KernelFactor

open SinhLogIntegral

private theorem density_continuous {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s => h a s / s) (Ioi 0) := by
  unfold h
  apply ContinuousOn.div
  · apply continuousOn_const.div
    · fun_prop
    · intro s hs
      exact ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr
        (div_pos (mul_pos Real.pi_pos hs) ha)))
  · exact continuousOn_id
  · intro s hs
    exact ne_of_gt hs

private theorem E_even (a : ℝ) : Function.Even (E a) := by
  intro t
  by_cases ht : t = 0
  · simp [ht]
  · simp [E, ht, mul_neg, Real.sinh_neg]

private theorem E_smooth {n : ℕ∞ω} {a : ℝ} (ha : 0 < a) : ContDiff ℝ n (E a) := by
  have he : E a = fun t => dslope Real.sinh 0 (a * t) := by
    funext t
    by_cases ht : t = 0
    · simp [ht, E, dslope_same, Real.deriv_sinh]
    · rw [dslope_of_ne _ (mul_ne_zero ha.ne' ht), slope_def_field]
      simp [E, ht, div_eq_mul_inv]
  rw [he]
  apply ContDiff.comp _ (contDiff_const.mul contDiff_id)
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    obtain ⟨p, hp⟩ := (Real.analyticAt_sinh : AnalyticAt ℝ Real.sinh 0)
    exact (show AnalyticAt ℝ (dslope Real.sinh 0) 0 from
      ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩).contDiffAt
  · have hh : dslope Real.sinh 0 =ᶠ[𝓝 x] fun y => Real.sinh y / y := by
      filter_upwards [eventually_ne_nhds hx] with y hy
      simp [dslope_of_ne _ hy, slope_def_field, div_eq_mul_inv]
    exact ((Real.contDiff_sinh.contDiffAt).div contDiffAt_id hx).congr_of_eventuallyEq hh

private theorem log_density_pd {ι : Type*} (s : Finset ι) (a w : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i)
    (hD : ∀ x, 0 < x → 0 ≤ ∑ i ∈ s, w i * h (a i) x) :
    PositiveDefinite (fun t =>
      (Real.exp (-(∑ i ∈ s, w i * Real.log (E (a i) t))) : ℂ)) := by
  have hi (t : ℝ) : IntegrableOn
      (fun x => (1 - Real.cos (t * x)) * (∑ i ∈ s, w i * h (a i) x) / x)
      (Ioi 0) := by
    have H := integrable_finsetSum s (fun i hi =>
      (integrable_logIntegrand (ha i hi) t).const_mul (w i))
    change Integrable _ _
    convert H using 1
    congr 1
    funext x
    simp only [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have H := LevyDensity.positiveDefinite hD
    (by
      intro n
      apply ContinuousOn.integrableOn_Icc
      have hh : Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ⊆ Ioi 0 := by
        intro x hx
        exact lt_of_lt_of_le (by positivity) hx.1
      have hc := continuousOn_finsetSum s (fun i hi =>
        (density_continuous (ha i hi)).const_mul (w i))
      convert hc.mono hh using 1
      funext x
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring)
    hi (r := 1) (by norm_num)
  convert H using 1
  funext t
  congr 2
  rw [neg_one_mul]
  congr 1
  calc
    _ = ∑ i ∈ s, w i * (2 * ∫ x in Ioi 0,
        (1 - Real.cos (t * x)) * h (a i) x / x) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [log_E_eq_integral (ha i hi)]
    _ = 2 * ∫ x in Ioi 0, ∑ i ∈ s,
        w i * ((1 - Real.cos (t * x)) * h (a i) x / x) := by
      rw [integral_finsetSum s (fun i hi =>
        (integrable_logIntegrand (ha i hi) t).const_mul (w i)), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul]
      ring
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        ring

/-- The density-balanced exponential factor. -/
def rho (p t : ℝ) : ℝ :=
  Real.exp (2 * Real.log (E p t) - (2 - 1 / p) * Real.log (E (p + 1) t) -
    Real.log (E 1 t) / p)

/-- The squared normalized hyperbolic sine ratio. -/
def phi (p t : ℝ) : ℝ := (E 1 t / E p t) ^ 2

private theorem rho_pd {p : ℝ} (hp : 1 ≤ p) :
    PositiveDefinite (fun t => (rho p t : ℂ)) := by
  have hp0 : 0 < p := by linarith
  have hq : 0 ≤ 2 - 1 / p := by
    have : 1 / p ≤ 1 := (div_le_one hp0).mpr hp
    linarith
  have H := log_density_pd (Finset.univ : Finset (Fin 3))
    ![p + 1, 1, p] ![2 - 1 / p, 1 / p, -2]
    (by intro i hi; fin_cases i <;> simp <;> linarith)
    (by
      intro x hx
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons,
        Fin.isValue]
      have hs := h_scale_le hp0 (show p ≤ p + 1 by linarith) hx
      have hmul := mul_le_mul_of_nonneg_left hs hq
      have halg : (2 - 1 / p) * ((p + 1) / p) - 2 = (p - 1) / p ^ 2 := by
        field_simp
        <;> ring
      have hd := (h_pos hp0 hx).le
      have hd1 := (h_pos (by norm_num : (0 : ℝ) < 1) hx).le
      have hrem : 0 ≤ ((2 - 1 / p) * ((p + 1) / p) - 2) * h p x := by
        rw [halg]
        exact mul_nonneg (div_nonneg (by linarith) (sq_nonneg _)) hd
      nlinarith [mul_nonneg (one_div_nonneg.mpr hp0.le) hd1])
  convert H using 1
  funext t
  simp [rho, Fin.sum_univ_three]
  <;> congr 2 <;> ring

private theorem reciprocal_pd :
    PositiveDefinite (fun t => ((E 1 t)⁻¹ ^ 2 : ℝ)) := by
  have H := log_density_pd (Finset.univ : Finset Unit) (fun _ => 1) (fun _ => 2)
    (by intros; norm_num) (by
      intro x hx
      simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        ((h_pos (by norm_num : (0 : ℝ) < 1) hx).le))
  convert H using 1
  funext t
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [show -(2 * Real.log (E 1 t)) = -(Real.log (E 1 t)) + -(Real.log (E 1 t)) by ring,
    Real.exp_add, Real.exp_neg, Real.exp_log (E_pos (by norm_num) t)]
  simp [pow_two]

private theorem phi_pd {p : ℝ} (hp : 1 ≤ p) :
    PositiveDefinite (fun t => (phi p t : ℂ)) := by
  have hp0 : 0 < p := by linarith
  have H := log_density_pd (Finset.univ : Finset (Fin 2)) ![p, 1] ![2, -2]
    (by intro i hi; fin_cases i <;> simp <;> linarith)
    (by
      intro x hx
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hh := h_scale_le (by norm_num : (0 : ℝ) < 1) hp hx
      have hd := (h_pos (by norm_num : (0 : ℝ) < 1) hx).le
      simp only [div_one] at hh
      nlinarith)
  convert H using 1
  funext t
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show -(2 * Real.log (E p t) + -2 * Real.log (E 1 t)) =
    (Real.log (E 1 t) - Real.log (E p t)) +
      (Real.log (E 1 t) - Real.log (E p t)) by ring,
    Real.exp_add, Real.exp_sub, Real.exp_log (E_pos (by norm_num) t),
    Real.exp_log (E_pos hp0 t)]
  simp [phi, pow_two]

/-- The positive definite product appearing in the curvature factorization. -/
def factor (p t : ℝ) : ℝ :=
  (1 / (p + 1)) * rho p t * (E 1 t)⁻¹ ^ 2 * SecondDifference.Q (phi p) t

/-- Each factor has a nonnegative logarithmic density or a positive quadratic deficit. -/
theorem factor_positiveDefinite {p : ℝ} (hp : 1 ≤ p) :
    PositiveDefinite (fun t => (factor p t : ℂ)) := by
  have hp0 : 0 < p := by linarith
  have he : Function.Even (phi p) := by
    intro t
    simp only [phi, E_even 1 t, E_even p t]
  have hc : ContDiff ℝ 2 (phi p) :=
    ((E_smooth (by norm_num)).div (E_smooth hp0)
      (fun t => (E_pos hp0 t).ne')).pow 2
  simpa only [factor, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv,
    Complex.ofReal_div, Complex.ofReal_one] using
    Closure.mul (Closure.mul (Closure.smul (rho_pd hp)
      (a := 1 / (p + 1)) (by positivity)) reciprocal_pd)
      (SecondDifference.Q_positiveDefinite he hc (phi_pd hp))

private theorem psi_E {γ : ℝ} (hγ : 2 ≤ γ) :
    Reduction.psi γ = fun t => (E γ t / E 1 t) ^ (1 / (γ - 1)) := by
  funext t
  by_cases ht : t = 0
  · simp [ht, Reduction.psi, Defs.stolarsky, E]
  have hγ0 : γ ≠ 0 := by linarith
  have hγ1 : γ ≠ 1 := by linarith
  have hab : Real.exp (-t) ≠ Real.exp t := by
    intro h
    have := Real.exp_injective h
    exact ht (by linarith)
  simp only [Reduction.psi, Defs.stolarsky, if_neg hab, if_neg hγ0, if_neg hγ1]
  congr 1
  simp only [← Real.exp_mul, E, if_neg ht, one_mul, Real.sinh_eq]
  have hsn : Real.exp t - Real.exp (-t) ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm hab)
  field_simp [ht, hγ0, hsn, sub_ne_zero.mpr hab]
  <;> ring

/-- The exponential Stolarsky profile is smooth across its removable diagonal. -/
theorem psi_contDiff {n : ℕ∞ω} {γ : ℝ} (hγ : 2 ≤ γ) :
    ContDiff ℝ n (Reduction.psi γ) := by
  rw [psi_E hγ]
  exact ((E_smooth (by linarith)).div (E_smooth (by norm_num))
    (fun t => (E_pos (by norm_num) t).ne')).rpow_const_of_ne
      (fun t => (div_pos (E_pos (by linarith) t)
        (E_pos (by norm_num) t)).ne')

private theorem rho_eq_profile {p : ℝ} (hp : 1 ≤ p) (t : ℝ) :
    rho p t = Reduction.psi (p + 1) t * (E p t / E (p + 1) t) ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hγ : 2 ≤ p + 1 := by linarith
  have he0 := E_pos (by norm_num : (0 : ℝ) < 1) t
  have hep := E_pos hp0 t
  have heγ := E_pos (by linarith : 0 < p + 1) t
  rw [psi_E hγ]
  apply Real.log_injOn_pos (Real.exp_pos _)
    (mul_pos (Real.rpow_pos_of_pos (div_pos heγ he0) _)
      (sq_pos_of_pos (div_pos hep heγ)))
  simp only [rho, Real.log_exp]
  rw [Real.log_mul
    (Real.rpow_pos_of_pos (div_pos heγ he0) _).ne'
    (sq_pos_of_pos (div_pos hep heγ)).ne',
    Real.log_rpow (div_pos heγ he0), Real.log_pow,
    Real.log_div heγ.ne' he0.ne', Real.log_div hep.ne' heγ.ne']
  simp only [add_sub_cancel_right]
  ring

private def logProfile (γ t : ℝ) : ℝ :=
  (Real.log (Real.sinh (γ * t)) - Real.log γ - Real.log (Real.sinh t)) / (γ - 1)

private def logSlope (γ t : ℝ) : ℝ :=
  (γ * Real.cosh (γ * t) / Real.sinh (γ * t) - Real.cosh t / Real.sinh t) / (γ - 1)

private def logCurvature (γ t : ℝ) : ℝ :=
  (1 / Real.sinh t ^ 2 - γ ^ 2 / Real.sinh (γ * t) ^ 2) / (γ - 1)

private theorem sinh_ne {a t : ℝ} (ha : a ≠ 0) (ht : t ≠ 0) :
    Real.sinh (a * t) ≠ 0 := by
  simpa only [ne_eq, Real.sinh_eq_zero] using mul_ne_zero ha ht

private theorem psi_exp {γ t : ℝ} (hγ : 2 ≤ γ) (ht : t ≠ 0) :
    Reduction.psi γ t = Real.exp (logProfile γ t) := by
  have hγ0 : γ ≠ 0 := by linarith
  have hst : Real.sinh t ≠ 0 := by simpa using ht
  have hsg := sinh_ne hγ0 ht
  rw [psi_E hγ]
  dsimp only
  rw [Real.rpow_def_of_pos
    (div_pos (E_pos (by linarith) t) (E_pos (by norm_num) t))]
  congr 1
  rw [Real.log_div (E_pos (by linarith) t).ne'
    (E_pos (by norm_num) t).ne']
  simp only [E, if_neg ht, one_mul]
  rw [Real.log_div hsg (mul_ne_zero hγ0 ht), Real.log_div hst ht,
    Real.log_mul hγ0 ht]
  unfold logProfile
  ring

private theorem psi_hasDerivAt {γ t : ℝ} (hγ : 2 ≤ γ) (ht : t ≠ 0) :
    HasDerivAt (Reduction.psi γ) (Reduction.psi γ t * logSlope γ t) t := by
  have hγ0 : γ ≠ 0 := by linarith
  have hsg := sinh_ne hγ0 ht
  have hst : Real.sinh t ≠ 0 := by simpa using ht
  have hd := (((((Real.hasDerivAt_sinh (γ * t)).comp t
    ((hasDerivAt_id t).const_mul γ)).log hsg).sub_const (Real.log γ)).sub
    ((Real.hasDerivAt_sinh t).log hst)).div_const (γ - 1)
  have he : Reduction.psi γ =ᶠ[𝓝 t] fun x => Real.exp (logProfile γ x) := by
    filter_upwards [eventually_ne_nhds ht] with x hx
    exact psi_exp hγ hx
  convert hd.exp.congr_of_eventuallyEq he using 1
  rw [psi_exp hγ ht]
  dsimp [logSlope, logProfile, Function.comp_def]
  ring

private theorem slope_hasDerivAt {γ t : ℝ} (hγ : 2 ≤ γ) (ht : t ≠ 0) :
    HasDerivAt (logSlope γ) (logCurvature γ t) t := by
  have hcoth (a : ℝ) (ha : a ≠ 0) :
      HasDerivAt (fun x => a * Real.cosh (a * x) / Real.sinh (a * x))
        (-(a ^ 2) / Real.sinh (a * t) ^ 2) t := by
    have hs := sinh_ne ha ht
    convert ((((Real.hasDerivAt_cosh (a * t)).comp t
      ((hasDerivAt_id t).const_mul a)).const_mul a).div
      ((Real.hasDerivAt_sinh (a * t)).comp t
        ((hasDerivAt_id t).const_mul a)) hs) using 1
    · funext x
      rfl
    · dsimp only [Function.comp_apply]
      field_simp
      linear_combination Real.cosh_sq_sub_sinh_sq (a * t)
  have hγ0 : γ ≠ 0 := by linarith
  convert ((hcoth γ hγ0).sub (hcoth 1 (by norm_num))).div_const (γ - 1) using 1
  · funext x
    simp [logSlope]
  · simp [logCurvature]
    ring

private theorem f_closed {γ t : ℝ} (hγ : 2 ≤ γ) (ht : t ≠ 0) :
    Reduction.f γ t = Reduction.psi γ t *
      (logSlope γ t ^ 2 + logCurvature γ t - 1) := by
  have he : deriv (Reduction.psi γ) =ᶠ[𝓝 t]
      fun x => Reduction.psi γ x * logSlope γ x := by
    filter_upwards [eventually_ne_nhds ht] with x hx
    exact (psi_hasDerivAt hγ hx).deriv
  have hh := ((psi_hasDerivAt hγ ht).mul (slope_hasDerivAt hγ ht)).congr_of_eventuallyEq he
  rw [Reduction.f, hh.deriv]
  ring

private theorem curvature_algebra {p t : ℝ} (hp : 1 ≤ p) (ht : t ≠ 0) :
    logSlope (p + 1) t ^ 2 + logCurvature (p + 1) t - 1 =
      (p + 1) / p ^ 2 *
        (Real.sinh (p * t) ^ 2 - p ^ 2 * Real.sinh t ^ 2) /
          (Real.sinh t ^ 2 * Real.sinh ((p + 1) * t) ^ 2) := by
  have hp0 : p ≠ 0 := by linarith
  have hγ0 : p + 1 ≠ 0 := by linarith
  have hst : Real.sinh t ≠ 0 := by simpa using ht
  have hsg := sinh_ne hγ0 ht
  have hs : Real.sinh (p * t) = Real.sinh ((p + 1) * t) * Real.cosh t -
      Real.cosh ((p + 1) * t) * Real.sinh t := by
    rw [← Real.sinh_sub]
    congr 1
    ring
  rw [hs]
  dsimp [logSlope, logCurvature]
  simp only [add_sub_cancel_right]
  field_simp [hp0, hst, hsg]
  linear_combination p * (p + 1) * Real.sinh t ^ 2 *
    Real.cosh_sq_sub_sinh_sq ((p + 1) * t) -
    p * Real.sinh ((p + 1) * t) ^ 2 * Real.cosh_sq_sub_sinh_sq t

private theorem factor_identity_ne {p t : ℝ} (hp : 1 ≤ p) (ht : t ≠ 0) :
    Reduction.f (p + 1) t = factor p t := by
  have hp0 : p ≠ 0 := by linarith
  have hγ0 : p + 1 ≠ 0 := by linarith
  have hst : Real.sinh t ≠ 0 := by simpa using ht
  have hsg := sinh_ne hγ0 ht
  have hsp := sinh_ne hp0 ht
  rw [f_closed (by linarith) ht, curvature_algebra hp ht]
  simp only [factor, rho_eq_profile hp, SecondDifference.Q, if_neg ht, phi,
    E, mul_zero, if_pos rfl, one_div_one, one_pow, one_mul]
  field_simp [hp0, hγ0, ht, hst, hsg, hsp]
  <;> ring

private theorem factor_continuous {p : ℝ} (hp : 1 ≤ p) : Continuous (factor p) := by
  have hp0 : 0 < p := by linarith
  have hc : ContDiff ℝ 2 (phi p) :=
    ((E_smooth (by norm_num)).div (E_smooth hp0)
      (fun t => (E_pos hp0 t).ne')).pow 2
  have he : Function.Even (phi p) := by
    intro t
    simp only [phi, E_even 1 t, E_even p t]
  have hq : Continuous (SecondDifference.Q (phi p)) := by
    have hh := hc.continuous_iteratedDeriv 2 (by norm_num)
    have H := continuous_parametric_integral_of_continuous
      (μ := volume)
      (f := fun t u : ℝ => (1 - u) * (-iteratedDeriv 2 (phi p) (u * t)))
      (by fun_prop) (s := Icc (0 : ℝ) 1) isCompact_Icc
    convert H using 1
    funext t
    rw [SecondDifference.Q_integral he hc, intervalIntegral.integral_of_le (by norm_num),
      integral_Icc_eq_integral_Ioc]
  have hr : Continuous (rho p) := by
    unfold rho
    apply Real.continuous_exp.comp
    exact ((continuous_const.mul ((E_smooth (n := 2) hp0).continuous.log
      (fun t => (E_pos hp0 t).ne'))).sub
      (continuous_const.mul ((E_smooth (n := 2) (by linarith)).continuous.log
        (fun t => (E_pos (by linarith) t).ne')))).sub
      (((E_smooth (n := 2) (by norm_num)).continuous.log
        (fun t => (E_pos (by norm_num) t).ne')).div_const p)
  unfold factor
  exact ((continuous_const.mul hr).mul
    (((E_smooth (n := 2) (by norm_num)).continuous.inv₀
      (fun t => (E_pos (by norm_num) t).ne')).pow 2)).mul hq

/-- The derivative defect equals the density-balanced quadratic-deficit product,
including its continuous value at zero. -/
theorem f_eq_factor {γ : ℝ} (hγ : 2 ≤ γ) :
    Reduction.f γ = factor (γ - 1) := by
  have hp : 1 ≤ γ - 1 := by linarith
  have hf : Continuous (Reduction.f γ) :=
    ((psi_contDiff hγ : ContDiff ℝ 2 (Reduction.psi γ)).deriv'
      : ContDiff ℝ 1 (deriv (Reduction.psi γ))).continuous_deriv (by norm_num)
        |>.sub (psi_contDiff (n := 2) hγ).continuous
  apply Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hf (factor_continuous hp)
  intro t ht
  have he := factor_identity_ne hp (show t ≠ 0 from ht)
  simpa only [sub_add_cancel] using he

/-- Positive definiteness of the Stolarsky derivative defect for every real
parameter at least two. -/
theorem positiveDefinite_f {γ : ℝ} (hγ : 2 ≤ γ) :
    PositiveDefinite (fun t => (Reduction.f γ t : ℂ)) := by
  rw [f_eq_factor hγ]
  exact factor_positiveDefinite (by linarith)

end D5.S3.Quantum.Matrix.StolarskyMean.KernelFactor
