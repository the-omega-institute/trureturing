/- GID: D5/S3/Analytic/Oscillation/BandLimitedWindowVariance
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/BandLimitedWindowVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Band-limited windows have unbounded Fourier variance and bounded derivative mass. -/

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import OmegaBuild.Commands

compile_only_with_mathlib

/-! Band-limited windows have unbounded Fourier variance and bounded derivative mass. -/

namespace D5.S3.Analytic.Oscillation.BandLimitedWindowVariance

noncomputable section

open MeasureTheory Set
open scoped Convolution FourierTransform SchwartzMap ContDiff ComplexConjugate


private def complexify (g : ℝ → ℝ) (u : ℝ) : ℂ := g u

private def window (R : ℝ) : ℝ → ℂ :=
  (Ioc (-R) R).indicator (fun _ => 1)

private def smoothCountWindow (R : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in x - R..x + R, φ y

private lemma window_integrable (R : ℝ) : Integrable (window R) := by
  rw [window, integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (hs := measure_Ioc_lt_top.ne)

private lemma fourier_window_smooth (R : ℝ) : ContDiff ℝ ∞ (𝓕 (window R)) := by
  apply Real.contDiff_fourier
  intro n _
  have he (x : ℝ) : ‖x‖ ^ n * ‖window R x‖ =
      (Ioc (-R) R).indicator (fun t : ℝ => ‖t‖ ^ n) x := by
    by_cases hx : x ∈ Ioc (-R) R <;> simp [window, hx]
  have h : Integrable ((Ioc (-R) R).indicator (fun t : ℝ => ‖t‖ ^ n)) :=
    (integrable_indicator_iff measurableSet_Ioc).2 (continuous_norm.pow n).integrableOn_Ioc
  exact h.congr (ae_of_all _ fun x => (he x).symm)

private lemma fourier_window_of_ne_zero {R ξ : ℝ} (hR : 0 ≤ R) (hξ : ξ ≠ 0) :
    𝓕 (window R) ξ = ((Real.sin (2 * Real.pi * ξ * R) / (Real.pi * ξ) : ℝ) : ℂ) := by
  let c := -(2 * Real.pi * ξ)
  have hc : c ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hξ)
  have he (x : ℝ) : Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) * window R x =
      (Ioc (-R) R).indicator (fun y : ℝ => Complex.exp (↑(c * y) * Complex.I)) x := by
    by_cases hx : x ∈ Ioc (-R) R
    · simp only [window, Set.indicator_of_mem hx, mul_one]
      congr 3
      dsimp [c]
      ring
    · simp [window, hx]
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_eq_mul, he]
  rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
  rw [intervalIntegral.integral_comp_mul_left (fun y : ℝ => Complex.exp (↑y * Complex.I)) hc,
    mul_neg, integral_exp_mul_I_eq_sin]
  rw [Complex.real_smul]
  dsimp [c]
  simp only [neg_mul, Real.sin_neg, inv_neg, Complex.ofReal_neg, neg_mul, mul_neg, neg_neg]
  push_cast
  field_simp

private lemma window_derivative (R : ℝ) {φ : ℝ → ℝ} (hφ : Continuous φ) (x : ℝ) :
    HasDerivAt (smoothCountWindow R φ) (φ (x + R) - φ (x - R)) x := by
  have h₁ := (hφ.integral_hasStrictDerivAt 0 (x + R)).hasDerivAt.comp x (hasDerivAt_id x |>.add_const R)
  have h₂ := (hφ.integral_hasStrictDerivAt 0 (x - R)).hasDerivAt.comp x (hasDerivAt_id x |>.sub_const R)
  convert (h₁.sub h₂) using 1
  · funext t
    change (∫ y in t - R..t + R, φ y) = (∫ y in 0..t + R, φ y) - ∫ y in 0..t - R, φ y
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hφ.intervalIntegrable 0 (t - R)) (hφ.intervalIntegrable (t - R) (t + R))
    linarith
  · simp

private lemma window_L1_variation (R : ℝ) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hi : Integrable φ) :
    Integrable (deriv (smoothCountWindow R φ)) ∧
      (∫ x : ℝ, ‖deriv (smoothCountWindow R φ) x‖) ≤ 2 * ∫ x : ℝ, ‖φ x‖ := by
  have he : deriv (smoothCountWindow R φ) = fun x => φ (x + R) - φ (x - R) :=
    funext fun x => (window_derivative R hφ x).deriv
  have hp := hi.comp_add_right R
  have hm : Integrable (fun x => φ (x - R)) := by
    simpa only [sub_eq_add_neg] using hi.comp_add_right (-R)
  rw [he]
  refine ⟨hp.sub hm, ?_⟩
  calc
    _ ≤ ∫ x : ℝ, ‖φ (x + R)‖ + ‖φ (x - R)‖ :=
      integral_mono (hp.sub hm).norm (hp.norm.add hm.norm) (fun _ => norm_sub_le _ _)
    _ = _ := by
      rw [integral_add hp.norm hm.norm]
      have h := integral_add_right_eq_self (fun x : ℝ => ‖φ x‖) (μ := volume) R
      have h' := integral_add_right_eq_self (fun x : ℝ => ‖φ x‖) (μ := volume) (-R)
      simp only [sub_eq_add_neg, h, h', two_mul]

private lemma window_convolution {R : ℝ} (hR : 0 ≤ R) (φ : ℝ → ℝ) :
    complexify (smoothCountWindow R φ) =
      window R ⋆[ContinuousLinearMap.mul ℂ ℂ] complexify φ := by
  funext x
  rw [convolution_def]
  change (↑(∫ y in x - R..x + R, φ y) : ℂ) = ∫ t : ℝ, window R t * (φ (x - t) : ℂ)
  have he (t : ℝ) :
      window R t * (φ (x - t) : ℂ) = (Ioc (-R) R).indicator (fun v => (φ (x - v) : ℂ)) t := by
    by_cases ht : t ∈ Ioc (-R) R <;> simp [window, ht]
  simp_rw [he]
  rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (by linarith : -R ≤ R),
    intervalIntegral.integral_comp_sub_left (fun v => (φ v : ℂ)) x,
    sub_neg_eq_add, intervalIntegral.integral_ofReal]

private lemma window_fourier {R : ℝ} (hR : 0 ≤ R) {φ : ℝ → ℝ} (hφ : Integrable φ) :
    𝓕 (complexify (smoothCountWindow R φ)) =
      fun u => 𝓕 (window R) u * 𝓕 (complexify φ) u := by
  rw [window_convolution hR]
  exact funext (Real.fourier_mul_convolution_eq (window_integrable R) hφ.ofReal)

private lemma window_schwartz {R : ℝ} (hR : 0 ≤ R) (φ : 𝓢(ℝ, ℝ))
    (hs : HasCompactSupport (𝓕 (complexify φ))) :
    ∃ g : 𝓢(ℝ, ℝ), (g : ℝ → ℝ) = smoothCountWindow R φ := by
  let φc : 𝓢(ℝ, ℂ) := SchwartzMap.postcompCLM Complex.ofRealCLM φ
  have hφc : 𝓕 (complexify φ) = ((𝓕 φc : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    rw [SchwartzMap.fourier_coe]
    rfl
  let f := 𝓕 (complexify (smoothCountWindow R φ))
  have hs₁ : HasCompactSupport f := by
    rw [show f = _ from window_fourier hR φ.integrable]
    apply IsCompact.of_isClosed_subset hs isClosed_closure
    exact tsupport_mul_subset_right
  have hs₂ : ContDiff ℝ ∞ f := by
    rw [show f = _ from window_fourier hR φ.integrable, hφc]
    exact (fourier_window_smooth R).mul ((𝓕 φc : 𝓢(ℝ, ℂ)).smooth (⊤ : ℕ∞))
  let F := hs₁.toSchwartzMap hs₂
  let G := (𝓕⁻ F : 𝓢(ℝ, ℂ))
  have hG : (G : ℝ → ℂ) = 𝓕⁻ f := SchwartzMap.fourierInv_coe _
  have hc : Continuous (smoothCountWindow R φ) :=
    continuous_iff_continuousAt.2 (fun x => (window_derivative R φ.continuous x).continuousAt)
  have hi : Integrable (complexify (smoothCountWindow R φ)) := by
    rw [window_convolution hR]
    exact (window_integrable R).integrable_convolution _ φ.integrable.ofReal
  have heq : 𝓕⁻ f = complexify (smoothCountWindow R φ) :=
    (Complex.continuous_ofReal.comp hc).fourierInv_fourier_eq hi F.integrable
  refine ⟨SchwartzMap.postcompCLM Complex.reCLM G, ?_⟩
  funext x
  change (G x).re = _
  rw [show G x = _ from congrFun (hG.trans heq) x]
  rfl

private lemma fourier_reflection (g : ℝ → ℝ) (ξ : ℝ) :
    𝓕 (fun u => complexify g (-u)) ξ = conj (𝓕 (complexify g) ξ) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul, ← integral_conj]
  calc
    _ = ∫ u : ℝ, Complex.exp (↑(-2 * Real.pi * (-u) * ξ) * Complex.I) * complexify g u := by
      simpa only [neg_neg] using
        (integral_neg_eq_self (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) *
          complexify g (-v)) volume).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      simp only [map_mul, complexify, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
      congr 2
      push_cast
      ring

private def bump : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

private def frequencyBump : 𝓢(ℝ, ℂ) :=
  (bump.hasCompactSupport.comp_left rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp bump.contDiff)

private def timeBump : 𝓢(ℝ, ℝ) :=
  SchwartzMap.postcompCLM Complex.reCLM (𝓕⁻ frequencyBump)

private lemma fourier_timeBump : 𝓕 (complexify timeBump) = complexify bump := by
  have hReal (ξ : ℝ) : conj (𝓕 (complexify bump) ξ) = 𝓕 (complexify bump) ξ := by
    rw [← fourier_reflection]
    have h := funext fun x => congrArg Complex.ofReal (bump.neg x)
    change (fun x => complexify bump (-x)) = complexify bump at h
    rw [h]
  have hT : complexify timeBump = ((𝓕⁻ frequencyBump : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    funext t
    have hpoint : (𝓕⁻ frequencyBump : 𝓢(ℝ, ℂ)) t = 𝓕 (complexify bump) (-t) := by
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
      rfl
    change ((Complex.re ((𝓕⁻ frequencyBump : 𝓢(ℝ, ℂ)) t) : ℝ) : ℂ) = _
    rw [hpoint]
    refine Complex.ext (Complex.ofReal_re _) ?_
    have hi := congrArg Complex.im (hReal (-t))
    simp only [Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith
  rw [hT, ← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  rfl

private def edge (n : ℕ) : ℝ := ((2 ^ n : ℕ) : ℝ) * Real.pi

private lemma edge_pos (n : ℕ) : 0 < edge n := by
  unfold edge
  exact mul_pos (by exact_mod_cast pow_pos (by decide : 0 < (2 : ℕ)) n) Real.pi_pos

private lemma edge_succ (n : ℕ) : edge (n + 1) = 2 * edge n := by
  simp only [edge, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
  ring

private lemma edge_mono : Monotone edge := by
  apply monotone_nat_of_le_succ
  intro n
  rw [edge_succ]
  linarith [edge_pos n]

private lemma sin_div_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => Real.sin t ^ 2 / t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact (Real.continuous_sin.pow 2).continuousOn.div continuous_id.continuousOn
    (fun t ht => (ha.trans_le ht.1).ne')

private lemma dyadic_block (n : ℕ) :
    (1 : ℝ) / 4 ≤ ∫ t in edge n..edge (n + 1), Real.sin t ^ 2 / t := by
  have hab := edge_mono (Nat.le_succ n)
  have hs (j : ℕ) : Real.sin (edge j) = 0 := Real.sin_nat_mul_pi _
  have hmass : (∫ t in edge n..edge (n + 1), Real.sin t ^ 2) = edge n / 2 := by
    simp only [integral_sin_sq, hs, zero_mul, sub_self, zero_add]
    rw [edge_succ]
    ring
  calc
    _ = (∫ t in edge n..edge (n + 1), (edge (n + 1))⁻¹ * Real.sin t ^ 2) := by
      rw [intervalIntegral.integral_const_mul, hmass, edge_succ]
      field_simp [(edge_pos n).ne']
      norm_num
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_on hab
        ((continuous_const.mul (Real.continuous_sin.pow 2)).intervalIntegrable _ _)
        (sin_div_integrable (edge_pos n) hab)
      intro t ht
      have ht0 := (edge_pos n).trans_le ht.1
      change (edge (n + 1))⁻¹ * Real.sin t ^ 2 ≤ Real.sin t ^ 2 / t
      rw [div_eq_mul_inv, mul_comm (edge (n + 1))⁻¹]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ ht0 ht.2) (sq_nonneg _)

private lemma lower_bound_dyadic (n : ℕ) : (n : ℝ) / 4 ≤ ∫ t in Real.pi..edge n, Real.sin t ^ 2 / t := by
  have h0 : edge 0 = Real.pi := by simp [edge]
  have hmono (j : ℕ) := h0 ▸ edge_mono (Nat.zero_le j)
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (sin_div_integrable Real.pi_pos (hmono n))
        (sin_div_integrable (edge_pos n) (edge_mono (Nat.le_succ n)))
    rw [← hsplit, Nat.cast_succ]
    linarith [dyadic_block n]

private lemma sine_variance_growth (w : ℝ → ℝ) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hweight : ∀ x ∈ Icc 0 δ, c ≤ w x) (n : ℕ) :
    ∃ a : ℝ, 0 < a ∧ c * ((n : ℝ) / 4) ≤
      ∫ x in (0 : ℝ)..1, w x * (Real.sin (a * x) ^ 2 / x) := by
  let a := edge n / δ
  let lo := Real.pi / a
  let q (x : ℝ) := Real.sin (a * x) ^ 2 / x
  have ha : 0 < a := div_pos (edge_pos n) hδ
  have hlo : 0 < lo := div_pos Real.pi_pos ha
  have haδ : a * δ = edge n := div_mul_cancel₀ _ hδ.ne'
  have haL : a * lo = Real.pi := by rw [mul_comm]; exact div_mul_cancel₀ _ ha.ne'
  have hloδ : lo ≤ δ := by
    have hmono := edge_mono (Nat.zero_le n)
    have h0 : edge 0 = Real.pi := by simp [edge]
    rw [h0] at hmono
    exact (div_le_iff₀ ha).2 (by simpa only [mul_comm δ a, haδ] using hmono)
  have hq_cont : Continuous q := by
    apply continuous_iff_continuousAt.2
    intro x
    by_cases hx : x = 0
    · subst x
      have hbound (x : ℝ) : ‖q x‖ ≤ a ^ 2 * ‖x‖ := by
        have hsin := Real.sin_sq_le_sq (x := a * x)
        by_cases hx : x = 0
        · simp [q, hx]
        · dsimp [q]
          rw [abs_div, abs_of_nonneg (sq_nonneg _)]
          apply (div_le_iff₀ (abs_pos.mpr hx)).2
          calc
            _ ≤ (a * x) ^ 2 := hsin
            _ = _ := by
              rw [mul_assoc, ← pow_two, sq_abs]
              ring
      have hz : q 0 = 0 := by simp [q]
      rw [ContinuousAt, hz]
      exact squeeze_zero_norm hbound (by simpa using (continuous_norm.continuousAt (x := (0 : ℝ))).tendsto.const_mul (a ^ 2))
    · exact ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2).continuousAt.div
        continuousAt_id hx
  have hscale : (∫ x in lo..δ, q x) = ∫ t in Real.pi..edge n, Real.sin t ^ 2 / t := by
    let f (t : ℝ) := Real.sin t ^ 2 / t
    have he (x : ℝ) : q x = a * f (a * x) := by
      dsimp [q, f]
      simp only [div_eq_mul_inv, mul_inv_rev]
      calc
        _ = Real.sin (a * x) ^ 2 * (x⁻¹ * (a * a⁻¹)) := by
          rw [mul_inv_cancel₀ ha.ne', mul_one]
        _ = _ := by ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left f ha.ne', haL, haδ, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  refine ⟨a, ha, ?_⟩
  calc
    _ ≤ c * (∫ x in lo..δ, q x) := mul_le_mul_of_nonneg_left
      (hscale ▸ lower_bound_dyadic n) hc.le
    _ = ∫ x in lo..δ, c * q x := (intervalIntegral.integral_const_mul _ _).symm
    _ ≤ ∫ x in lo..δ, w x * q x := by
      apply intervalIntegral.integral_mono_on hloδ
        ((continuous_const.mul hq_cont).intervalIntegrable _ _) ((hw.mul hq_cont).intervalIntegrable _ _)
      intro x hx
      exact mul_le_mul_of_nonneg_right (hweight x ⟨hlo.le.trans hx.1, hx.2⟩)
        (div_nonneg (sq_nonneg _) (hlo.le.trans hx.1))
    _ ≤ ∫ x in (0 : ℝ)..1, w x * q x := by
      apply intervalIntegral.integral_mono_interval hlo.le hloδ hδ1 _ ((hw.mul hq_cont).intervalIntegrable _ _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (hw0 x) (div_nonneg (sq_nonneg _) hx.1.le)

private lemma spectral_variance_integrable (g : 𝓢(ℝ, ℝ)) :
    Integrable (fun u : ℝ => |u| * ‖𝓕 (complexify g) u‖ ^ 2) := by
  let gc : 𝓢(ℝ, ℂ) := SchwartzMap.postcompCLM Complex.ofRealCLM g
  let G := (𝓕 gc : 𝓢(ℝ, ℂ))
  change Integrable (fun u : ℝ => |u| * ‖𝓕 (complexify g) u‖ ^ 2)
  have hG : (G : ℝ → ℂ) = 𝓕 (complexify g) := SchwartzMap.fourier_coe _
  rw [← hG]
  have hi : Integrable (fun u : ℝ => |u| * ‖G u‖) := by
    simpa only [pow_one, Real.norm_eq_abs] using G.integrable_pow_mul volume 1
  let M := (SchwartzMap.seminorm ℝ 0 0) G
  refine (hi.const_mul M).mono' (by fun_prop) (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
  have h := SchwartzMap.norm_le_seminorm ℝ G u
  calc
    _ = ‖G u‖ * (|u| * ‖G u‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h (mul_nonneg (abs_nonneg _) (norm_nonneg _))

private theorem window_spectral_variance_unbounded (n : ℕ) : ∃ g : 𝓢(ℝ, ℝ),
    (∀ u, 1 < |u| → 𝓕 (complexify g) u = 0) ∧
    (∫ x, ‖deriv g x‖) ≤ 2 * (∫ x, ‖timeBump x‖) ∧
    (n : ℝ) / (4 * Real.pi ^ 2) ≤ ∫ u : ℝ, |u| * ‖𝓕 (complexify g) u‖ ^ 2 := by
  have hBump (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (1 / 4)) : bump u = 1 := by
    apply bump.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg hu.1]
    exact hu.2
  obtain ⟨a, ha, hlarge⟩ := sine_variance_growth
    (fun u => ‖bump u‖ ^ 2) (bump.continuous.norm.pow 2) (fun _ => sq_nonneg _)
    1 (1 / 4) zero_lt_one (by norm_num) (by norm_num)
    (fun u hu => by rw [hBump u hu]; norm_num) n
  let R := a / (2 * Real.pi)
  have hR : 0 ≤ R := div_nonneg ha.le (by positivity)
  have hCompact : HasCompactSupport (𝓕 (complexify timeBump)) := by
    rw [fourier_timeBump]
    exact bump.hasCompactSupport.comp_left rfl
  obtain ⟨g, hg⟩ := window_schwartz hR timeBump hCompact
  have hFourier :
      𝓕 (complexify g) = fun u => 𝓕 (window R) u * (bump u : ℂ) := by
    rw [hg, window_fourier hR timeBump.integrable, fourier_timeBump]
    rfl
  refine ⟨g, ?_, ?_, ?_⟩
  · intro u hu
    rw [hFourier]
    have hz : bump u = 0 := bump.zero_of_le_dist (by
      rw [Real.dist_eq, sub_zero]
      change (1 : ℝ) / 2 ≤ |u|
      linarith)
    simp [hz]
  · rw [hg]
    exact (window_L1_variation R timeBump.continuous timeBump.integrable).2
  · let f (u : ℝ) : ℝ := |u| * ‖𝓕 (complexify g) u‖ ^ 2
    have hi : Integrable f := spectral_variance_integrable g
    have hpoint (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) 1) :
        ‖bump u‖ ^ 2 * (Real.sin (a * u) ^ 2 / u) = Real.pi ^ 2 * f u := by
      have harg : 2 * Real.pi * u * R = a * u := by
        dsimp [R]
        field_simp [Real.pi_ne_zero]
      dsimp [f]
      simp only [congrFun hFourier u, fourier_window_of_ne_zero hR hu.1.ne', harg, norm_mul,
        Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs, abs_of_nonneg hu.1.le]
      field_simp [hu.1.ne', Real.pi_ne_zero]
    have heq :
        (∫ u in (0 : ℝ)..1, ‖bump u‖ ^ 2 * (Real.sin (a * u) ^ 2 / u)) =
          Real.pi ^ 2 * ∫ u in Ioc (0 : ℝ) 1, f u := by
      rw [intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioc hpoint
    have htotal : (∫ u in Ioc (0 : ℝ) 1, f u) ≤ ∫ u, f u :=
      setIntegral_le_integral hi (ae_of_all _ fun u => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    rw [heq, one_mul] at hlarge
    apply (div_le_iff₀ (show 0 < 4 * Real.pi ^ 2 by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left htotal (sq_nonneg Real.pi)]

/-- Real band-limited Schwartz windows have arbitrarily large weighted Fourier energy
while their derivatives have a common L¹ bound. -/
theorem exists_windows_with_unbounded_spectral_variance :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, ∃ g : 𝓢(ℝ, ℝ),
      (∀ u : ℝ, 1 < |u| → 𝓕 (fun x => (g x : ℂ)) u = 0) ∧
      (∫ x, ‖deriv g x‖) ≤ K ∧
      (n : ℝ) / (4 * Real.pi ^ 2) ≤ ∫ u : ℝ, |u| * ‖𝓕 (fun x => (g x : ℂ)) u‖ ^ 2 := by
  refine ⟨2 * ∫ x : ℝ, ‖timeBump x‖, mul_nonneg (by norm_num)
    (integral_nonneg fun _ => norm_nonneg _), ?_⟩
  exact window_spectral_variance_unbounded


end
end D5.S3.Analytic.Oscillation.BandLimitedWindowVariance
