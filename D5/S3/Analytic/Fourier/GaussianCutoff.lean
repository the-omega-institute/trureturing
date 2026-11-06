/- GID: D5/S3/Analytic/Fourier/GaussianCutoff
   generality: G
   mirror-B: D5/B/S3/Analytic/Fourier/GaussianCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Smooth even frequency cutoffs yield real Schwartz kernels with bounded multipliers. -/

import D5.S3.Analytic.Fourier.AngularFejerKernel
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Smooth angular cutoffs, their real Schwartz kernels, and uniform kernel tails. -/

namespace D5.S3.Analytic.Fourier.GaussianCutoff

open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff

noncomputable section

def cutoffWidth (M : ℝ) : ℝ := M ^ (1 / 4 : ℝ)

def χ (M t : ℝ) : ℝ :=
  (1 - Real.smoothTransition ((t - M) / cutoffWidth M)) *
    (1 - Real.smoothTransition ((-t - M) / cutoffWidth M))

def cutoffMultiplier (M t : ℝ) : ℝ := Real.exp (t ^ 2 / (2 * M ^ 2)) * χ M t

private lemma width_pos {M : ℝ} (hM : 0 < M) : 0 < cutoffWidth M :=
  Real.rpow_pos_of_pos hM _

private lemma width_le {M : ℝ} (hM : 1 ≤ M) : cutoffWidth M ≤ M := by
  simpa [cutoffWidth] using Real.rpow_le_rpow_of_exponent_le hM
    (show (1 / 4 : ℝ) ≤ 1 by norm_num)

theorem chi_nonneg (M t : ℝ) : 0 ≤ χ M t :=
  mul_nonneg (sub_nonneg.mpr (Real.smoothTransition.le_one _))
    (sub_nonneg.mpr (Real.smoothTransition.le_one _))

theorem chi_le_one (M t : ℝ) : χ M t ≤ 1 := by
  have h₁ := Real.smoothTransition.nonneg ((t - M) / cutoffWidth M)
  have h₂ := Real.smoothTransition.nonneg ((-t - M) / cutoffWidth M)
  have h₃ := Real.smoothTransition.le_one ((-t - M) / cutoffWidth M)
  have h := mul_le_mul_of_nonneg_right (show 1 - Real.smoothTransition
    ((t - M) / cutoffWidth M) ≤ 1 by linarith) (show 0 ≤ 1 - Real.smoothTransition
    ((-t - M) / cutoffWidth M) by linarith)
  dsimp [χ]
  nlinarith

theorem chi_even (M t : ℝ) : χ M (-t) = χ M t := by
  simp only [χ, neg_neg, mul_comm]

theorem chi_eq_one {M t : ℝ} (hM : 0 < M) (ht : |t| ≤ M) : χ M t = 1 := by
  have h₁ : (t - M) / cutoffWidth M ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith [(abs_le.mp ht).2]) (width_pos hM).le
  have h₂ : (-t - M) / cutoffWidth M ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith [(abs_le.mp ht).1]) (width_pos hM).le
  simp [χ, Real.smoothTransition.zero_of_nonpos h₁,
    Real.smoothTransition.zero_of_nonpos h₂]

theorem chi_eq_zero {M t : ℝ} (hM : 0 < M)
    (ht : M + cutoffWidth M ≤ |t|) : χ M t = 0 := by
  rcases le_or_gt 0 t with h | h
  · have harg : 1 ≤ (t - M) / cutoffWidth M := by
      rw [le_div_iff₀ (width_pos hM)]
      rw [abs_of_nonneg h] at ht
      linarith
    simp [χ, Real.smoothTransition.one_of_one_le harg]
  · have harg : 1 ≤ (-t - M) / cutoffWidth M := by
      rw [le_div_iff₀ (width_pos hM)]
      rw [abs_of_neg h] at ht
      linarith
    simp [χ, Real.smoothTransition.one_of_one_le harg]

theorem chi_contDiff (M : ℝ) : ContDiff ℝ ∞ (χ M) := by
  unfold χ
  exact (contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const _))).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.neg.sub contDiff_const).div_const _)))

theorem cutoff_multiplier_contDiff (M : ℝ) : ContDiff ℝ ∞ (cutoffMultiplier M) := by
  exact (((contDiff_id.pow 2).div_const _).exp).mul (chi_contDiff M)

theorem cutoff_multiplier_hasCompactSupport {M : ℝ} (hM : 0 < M) :
    HasCompactSupport (cutoffMultiplier M) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(M + cutoffWidth M))
    (b := M + cutoffWidth M))
  intro t ht
  have h : M + cutoffWidth M ≤ |t| := by
    by_contra hn
    apply ht
    exact ⟨by linarith [(abs_le.mp (le_of_lt (lt_of_not_ge hn))).1],
      by linarith [(abs_le.mp (le_of_lt (lt_of_not_ge hn))).2]⟩
  simp [cutoffMultiplier, chi_eq_zero hM h]

theorem cutoff_multiplier_even (M t : ℝ) : cutoffMultiplier M (-t) = cutoffMultiplier M t := by
  simp [cutoffMultiplier, chi_even]

private lemma cutoff_multiplier_nonneg (M t : ℝ) : 0 ≤ cutoffMultiplier M t :=
  mul_nonneg (Real.exp_pos _).le (chi_nonneg M t)

private lemma cutoff_multiplier_le {M : ℝ} (hM : 1 ≤ M) (t : ℝ) :
    cutoffMultiplier M t ≤ Real.exp 2 := by
  by_cases ht : M + cutoffWidth M ≤ |t|
  · simp [cutoffMultiplier, chi_eq_zero (by linarith : 0 < M) ht, (Real.exp_pos 2).le]
  have ht' : |t| ≤ 2 * M := by linarith [width_le hM, lt_of_not_ge ht]
  have hsq : t ^ 2 ≤ 4 * M ^ 2 := by
    have := sq_le_sq₀ (abs_nonneg t) (by linarith : 0 ≤ 2 * M) |>.2 ht'
    nlinarith [sq_abs t]
  have he : t ^ 2 / (2 * M ^ 2) ≤ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * M ^ 2)).2
    nlinarith
  exact (mul_le_of_le_one_right (Real.exp_pos _).le (chi_le_one M t)).trans
    (Real.exp_le_exp.mpr he)

private def multiplierSchwartzPos (M : ℝ) (hM : 0 < M) : SchwartzMap ℝ ℂ :=
  ((cutoff_multiplier_hasCompactSupport hM).comp_left (g := Complex.ofReal) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (cutoff_multiplier_contDiff M))

def cutoffMultiplierSchwartz (M : ℝ) : SchwartzMap ℝ ℂ :=
  if hM : 0 < M then
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (2 * Real.pi) (by positivity)))
      (multiplierSchwartzPos M hM)
  else 0

def cutoffKernelSchwartz (M : ℝ) : SchwartzMap ℝ ℂ := 𝓕⁻ (cutoffMultiplierSchwartz M)

def cutoffKernel (M v : ℝ) : ℝ := (cutoffKernelSchwartz M v).re

private lemma multiplierSchwartz_apply {M : ℝ} (hM : 0 < M) (ξ : ℝ) :
    cutoffMultiplierSchwartz M ξ = (cutoffMultiplier M (2 * Real.pi * ξ) : ℂ) := by
  simp only [cutoffMultiplierSchwartz, dite_eq_left hM,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    multiplierSchwartzPos, ContinuousLinearEquiv.unitsEquivAut_apply, mul_comm ξ,
    HasCompactSupport.toSchwartzMap, Units.val_mk0, Function.comp_apply]
  rfl

private lemma multiplierSchwartz_even (M ξ : ℝ) :
    cutoffMultiplierSchwartz M (-ξ) = cutoffMultiplierSchwartz M ξ := by
  by_cases hM : 0 < M
  · simp only [multiplierSchwartz_apply hM, mul_neg, cutoff_multiplier_even]
  · simp [cutoffMultiplierSchwartz, hM]

private lemma multiplierSchwartz_real (M ξ : ℝ) :
    (starRingEnd ℂ) (cutoffMultiplierSchwartz M ξ) = cutoffMultiplierSchwartz M ξ := by
  by_cases hM : 0 < M
  · simp [multiplierSchwartz_apply hM]
  · simp [cutoffMultiplierSchwartz, hM]

private lemma kernel_real (M v : ℝ) : star (cutoffKernelSchwartz M v) =
    cutoffKernelSchwartz M v := by
  change star (𝓕⁻ (cutoffMultiplierSchwartz M) v) = 𝓕⁻ (cutoffMultiplierSchwartz M) v
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  change (starRingEnd ℂ) (∫ ξ : ℝ, _) = _
  rw [← integral_conj]
  rw [← integral_neg_eq_self (fun ξ : ℝ =>
    Complex.exp ((↑(2 * Real.pi * inner ℝ ξ v) : ℂ) * Complex.I) •
      cutoffMultiplierSchwartz M ξ)]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp [smul_eq_mul, map_mul, map_ofNat, ← Complex.exp_conj, multiplierSchwartz_real,
    multiplierSchwartz_even]

theorem cutoff_kernelSchwartz_coe (M v : ℝ) :
    cutoffKernelSchwartz M v = (cutoffKernel M v : ℂ) := by
  have hi : (cutoffKernelSchwartz M v).im = 0 := by
    have := congrArg Complex.im (kernel_real M v)
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  exact Complex.ext rfl (by simpa using hi)

theorem cutoff_kernel_integrable (M : ℝ) : Integrable (cutoffKernel M) :=
  (cutoffKernelSchwartz M).integrable.re

private lemma kernel_fourier {M : ℝ} (hM : 0 < M) (ξ : ℝ) :
    𝓕 (fun v => (cutoffKernel M v : ℂ)) ξ =
      (cutoffMultiplier M (2 * Real.pi * ξ) : ℂ) := by
  have he : (fun v => (cutoffKernel M v : ℂ)) = (cutoffKernelSchwartz M : ℝ → ℂ) :=
    funext (fun v => (cutoff_kernelSchwartz_coe M v).symm)
  rw [he, ← SchwartzMap.fourier_coe]
  change 𝓕 (𝓕⁻ (cutoffMultiplierSchwartz M)) ξ = _
  rw [FourierTransform.fourier_fourierInv_eq, multiplierSchwartz_apply hM]

private lemma angular_kernel_transform {M : ℝ} (hM : 0 < M) (γ : ℝ) :
    (∫ v : ℝ, Complex.exp ((↑(-γ * v) : ℂ) * Complex.I) * (cutoffKernel M v : ℂ)) =
      (cutoffMultiplier M γ : ℂ) := by
  have h := kernel_fourier hM (γ / (2 * Real.pi))
  rw [Real.fourier_real_eq_integral_exp_smul] at h
  have he (v : ℝ) : -2 * Real.pi * v * (γ / (2 * Real.pi)) = -γ * v := by
    field_simp
  simpa only [smul_eq_mul, he, mul_div_cancel₀ γ (by positivity : 2 * Real.pi ≠ 0)] using h

theorem cutoff_kernel_cos {M : ℝ} (hM : 1 ≤ M) (γ y : ℝ) :
    (∫ v : ℝ, cutoffKernel M v * Real.cos (γ * (y - v))) =
      Real.exp (γ ^ 2 / (2 * M ^ 2)) * χ M γ * Real.cos (γ * y) := by
  have hft (t : ℝ) : AngularFejerKernel.aft (cutoffKernel M) t =
      (cutoffMultiplier M t : ℂ) := by
    unfold AngularFejerKernel.aft
    calc
      _ = ∫ v : ℝ, Complex.exp ((↑(-t * v) : ℂ) * Complex.I) *
          (cutoffKernel M v : ℂ) := by
        apply integral_congr_ae
        filter_upwards with v
        have hex : -Complex.I * (t : ℂ) * v = ((-t * v : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [hex, mul_comm]
      _ = _ := angular_kernel_transform (by linarith : 0 < M) t
  have hc := AngularFejerKernel.cosine_convolution (cutoff_kernel_integrable M) hft γ y
  calc
    _ = ∫ u : ℝ, cutoffKernel M (y - u) * Real.cos (γ * (y - (y - u))) :=
      (integral_sub_left_eq_self
        (fun v : ℝ => cutoffKernel M v * Real.cos (γ * (y - v))) volume y).symm
    _ = _ := by simpa only [sub_sub_cancel, mul_comm, cutoffMultiplier] using hc

theorem cutoff_multiplier_bound {M : ℝ} (hM : 1 ≤ M) (ξ : ℝ) :
    ‖𝓕 (fun v => (cutoffKernel M v : ℂ)) ξ‖ ≤ Real.exp 2 := by
  have he : (fun v => (cutoffKernel M v : ℂ)) = (cutoffKernelSchwartz M : ℝ → ℂ) :=
    funext (fun v => (cutoff_kernelSchwartz_coe M v).symm)
  rw [he, ← SchwartzMap.fourier_coe]
  change ‖𝓕 (𝓕⁻ (cutoffMultiplierSchwartz M)) ξ‖ ≤ _
  rw [FourierTransform.fourier_fourierInv_eq, multiplierSchwartz_apply (by linarith : 0 < M)]
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (cutoff_multiplier_nonneg M _)] using cutoff_multiplier_le hM (2 * Real.pi * ξ)

private lemma transition_deriv_zero (n : ℕ) (hn : n ≠ 0) {x : ℝ}
    (hx : x < 0 ∨ 1 < x) : iteratedDeriv n Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · have he : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [gt_mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [he.iteratedDeriv_eq n]
    simp
  · have he : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    rw [he.iteratedDeriv_eq n]
    simp [iteratedDeriv_const, hn]

theorem smoothTransition_derivatives_bounded (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |iteratedDeriv n Real.smoothTransition x| ≤ C := by
  by_cases hn : n = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x
    simpa [hn, abs_of_nonneg (Real.smoothTransition.nonneg x)] using
      Real.smoothTransition.le_one x
  have hc : Continuous (iteratedDeriv n Real.smoothTransition) :=
    Real.smoothTransition.contDiff.continuous_iteratedDeriv' n
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact (hC x hx).trans (le_max_left _ _)
  · rw [transition_deriv_zero n hn (by simpa only [mem_Icc, not_and_or, not_le] using hx),
      abs_zero]
    exact le_trans zero_le_one (le_max_right _ _)

private def gaussianProfile (x : ℝ) : ℝ := Real.exp (x ^ 2 / 2)

private def transitionProfile (x : ℝ) : ℝ := 1 - Real.smoothTransition x

private lemma gaussianProfile_smooth : ContDiff ℝ ∞ gaussianProfile := by
  unfold gaussianProfile
  fun_prop

private lemma transitionProfile_smooth : ContDiff ℝ ∞ transitionProfile :=
  contDiff_const.sub Real.smoothTransition.contDiff

private lemma gaussianProfile_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc (-2 : ℝ) 2, |iteratedDeriv n gaussianProfile x| ≤ C := by
  have hc := gaussianProfile_smooth.continuous_iteratedDeriv n (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hc.continuousOn
  exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun x hx => (hC x hx).trans (le_max_left _ _)⟩

private lemma transitionProfile_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, |iteratedDeriv n transitionProfile x| ≤ C := by
  by_cases hn : n = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x
    simp only [hn, iteratedDeriv_zero, transitionProfile,
      abs_of_nonneg (sub_nonneg.mpr (Real.smoothTransition.le_one x))]
    linarith [Real.smoothTransition.nonneg x]
  obtain ⟨C, hC, hb⟩ := smoothTransition_derivatives_bounded n
  refine ⟨C, hC, fun x => ?_⟩
  rw [show transitionProfile = (fun x => 1 - Real.smoothTransition x) from rfl,
    iteratedDeriv_const_sub (Nat.pos_of_ne_zero hn)]
  simpa using hb x

private lemma affine_deriv (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (n : ℕ) (a d t : ℝ) :
    iteratedDeriv n (fun t => f ((t - a) / d)) t =
      d⁻¹ ^ n * iteratedDeriv n f ((t - a) / d) := by
  have he : (fun t => f ((t - a) / d)) = (fun t => (fun x => f (d⁻¹ * x)) (t - a)) := by
    ext x
    congr 1
    ring
  rw [he, iteratedDeriv_comp_sub_const n (fun x => f (d⁻¹ * x)) a,
    iteratedDeriv_comp_const_mul (hf.of_le (by exact_mod_cast le_top))]
  simp only [div_eq_mul_inv, mul_comm]

private lemma multiplier_deriv_center {M t : ℝ} (hM : 0 < M) (ht : |t| < M) :
    iteratedDeriv 5 (cutoffMultiplier M) t =
      M⁻¹ ^ 5 * iteratedDeriv 5 gaussianProfile (t / M) := by
  have he : cutoffMultiplier M =ᶠ[𝓝 t] (fun t => gaussianProfile (t / M)) := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds ht] with x hx
    rw [cutoffMultiplier, chi_eq_one hM hx.le, mul_one]
    dsimp [gaussianProfile]
    congr 1
    field_simp
  rw [he.iteratedDeriv_eq 5]
  simpa using affine_deriv gaussianProfile gaussianProfile_smooth 5 0 M t

private lemma multiplier_deriv_band {M t : ℝ} (hM : 0 < M) (ht : 0 ≤ t) :
    iteratedDeriv 5 (cutoffMultiplier M) t =
      ∑ i ∈ Finset.range 6, (Nat.choose 5 i : ℝ) *
        (M⁻¹ ^ i * iteratedDeriv i gaussianProfile (t / M)) *
        ((cutoffWidth M)⁻¹ ^ (5 - i) *
          iteratedDeriv (5 - i) transitionProfile ((t - M) / cutoffWidth M)) := by
  have he : cutoffMultiplier M =ᶠ[𝓝 t]
      (fun t => gaussianProfile (t / M) * transitionProfile ((t - M) / cutoffWidth M)) := by
    filter_upwards [lt_mem_nhds (show -M < t by linarith)] with x hx
    have ha : (-x - M) / cutoffWidth M ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (width_pos hM).le
    have hg : Real.exp (x ^ 2 / (2 * M ^ 2)) = gaussianProfile (x / M) := by
      unfold gaussianProfile
      congr 1
      field_simp
    simp only [cutoffMultiplier, χ, Real.smoothTransition.zero_of_nonpos ha,
      sub_zero, mul_one, transitionProfile, hg]
  rw [he.iteratedDeriv_eq 5, iteratedDeriv_fun_mul]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [show (fun t => gaussianProfile (t / M)) = (fun t => gaussianProfile ((t - 0) / M)) by simp]
    rw [affine_deriv gaussianProfile gaussianProfile_smooth,
      affine_deriv transitionProfile transitionProfile_smooth]
    simp
  · exact (gaussianProfile_smooth.comp (contDiff_id.div_const _)).contDiffAt.of_le
      (by decide)
  · exact (transitionProfile_smooth.comp
      ((contDiff_id.sub contDiff_const).div_const _)).contDiffAt.of_le (by decide)

private lemma multiplier_deriv_bounds :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ M : ℝ, 1 ≤ M → ∀ t : ℝ, 0 ≤ t →
      (t < M → |iteratedDeriv 5 (cutoffMultiplier M) t| ≤ A * M⁻¹ ^ 5) ∧
      (t ≤ M + cutoffWidth M →
        |iteratedDeriv 5 (cutoffMultiplier M) t| ≤ B * (cutoffWidth M)⁻¹ ^ 5) := by
  choose G hGp hG using gaussianProfile_bound
  choose U hUp hU using transitionProfile_bound
  let B := ∑ i ∈ Finset.range 6, (Nat.choose 5 i : ℝ) * G i * U (5 - i)
  have hB : 0 < B := by
    apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hGp i).le) (hUp _).le
    · refine ⟨0, by simp, ?_⟩
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, tsub_zero]
      exact mul_pos (hGp 0) (hUp 5)
  refine ⟨G 5, B, hGp 5, hB, fun M hM t ht => ?_⟩
  have hMp : 0 < M := by linarith
  have hd := width_pos hMp
  have hdM : M⁻¹ ≤ (cutoffWidth M)⁻¹ := (inv_le_inv₀ hMp hd).2 (width_le hM)
  constructor
  · intro htc
    rw [multiplier_deriv_center hMp (by simpa [abs_of_nonneg ht] using htc), abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ M⁻¹ ^ 5)]
    have harg : t / M ∈ Icc (-2 : ℝ) 2 := by
      constructor
      · exact le_trans (by norm_num) (div_nonneg ht hMp.le)
      · apply (div_le_iff₀ hMp).2
        linarith
    exact (mul_le_mul_of_nonneg_left (hG 5 (t / M) harg) (by positivity)).trans_eq (mul_comm _ _)
  · intro htb
    have harg : t / M ∈ Icc (-2 : ℝ) 2 := by
      constructor
      · exact le_trans (by norm_num) (div_nonneg ht hMp.le)
      · apply (div_le_iff₀ hMp).2
        linarith [width_le hM]
    rw [multiplier_deriv_band hMp ht]
    calc
      _ ≤ ∑ i ∈ Finset.range 6, |(Nat.choose 5 i : ℝ) *
          (M⁻¹ ^ i * iteratedDeriv i gaussianProfile (t / M)) *
          ((cutoffWidth M)⁻¹ ^ (5 - i) *
            iteratedDeriv (5 - i) transitionProfile ((t - M) / cutoffWidth M))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range 6,
          ((Nat.choose 5 i : ℝ) * G i * U (5 - i)) * (cutoffWidth M)⁻¹ ^ 5 := by
        apply Finset.sum_le_sum
        intro i hi
        have hi5 : i ≤ 5 := by have := Finset.mem_range.mp hi; omega
        have hGi := hGp i
        have hUi := hUp (5 - i)
        simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (Nat.choose 5 i) : (0 : ℝ) ≤ _),
          abs_of_nonneg (by positivity : 0 ≤ M⁻¹ ^ i),
          abs_of_nonneg (by positivity : 0 ≤ (cutoffWidth M)⁻¹ ^ (5 - i))]
        calc
          _ ≤ (Nat.choose 5 i : ℝ) * ((cutoffWidth M)⁻¹ ^ i * G i) *
              ((cutoffWidth M)⁻¹ ^ (5 - i) * U (5 - i)) := by
            gcongr
            · exact hG i (t / M) harg
            · exact hU (5 - i) _
          _ = ((Nat.choose 5 i : ℝ) * G i * U (5 - i)) *
              ((cutoffWidth M)⁻¹ ^ i * (cutoffWidth M)⁻¹ ^ (5 - i)) := by ring
          _ = _ := by rw [← pow_add, Nat.add_sub_of_le hi5]
      _ = B * (cutoffWidth M)⁻¹ ^ 5 := (Finset.sum_mul ..).symm

private lemma multiplier_deriv_integrable {M : ℝ} (hM : 0 < M) (n : ℕ) :
    Integrable (fun t => |iteratedDeriv n (cutoffMultiplier M) t|) := by
  have h := ((cutoff_multiplier_hasCompactSupport hM).toSchwartzMap
    (cutoff_multiplier_contDiff M)).integrable_pow_mul_iteratedFDeriv volume 0 n
  change Integrable (fun t : ℝ => ‖t‖ ^ 0 * ‖iteratedFDeriv ℝ n (cutoffMultiplier M) t‖) at h
  simpa only [pow_zero, one_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    using h

private lemma multiplier_deriv_abs (M t : ℝ) :
    |iteratedDeriv 5 (cutoffMultiplier M) (|t|)| = |iteratedDeriv 5 (cutoffMultiplier M) t| := by
  have he : (fun t => cutoffMultiplier M (-t)) = cutoffMultiplier M :=
    funext (cutoff_multiplier_even M)
  have h := iteratedDeriv_comp_neg 5 (cutoffMultiplier M) t
  rw [he] at h
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), h]
    simp

private lemma multiplier_deriv_zero {M t : ℝ} (hM : 0 < M)
    (ht : M + cutoffWidth M < |t|) : iteratedDeriv 5 (cutoffMultiplier M) t = 0 := by
  have he : cutoffMultiplier M =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds ht] with x hx
    simp [cutoffMultiplier, chi_eq_zero hM hx.le]
  rw [he.iteratedDeriv_eq 5]
  simp

private lemma width_fourth {M : ℝ} (hM : 0 < M) : cutoffWidth M ^ 4 = M := by
  rw [cutoffWidth, ← Real.rpow_natCast, ← Real.rpow_mul hM.le]
  norm_num

private lemma multiplier_derivative_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 1 ≤ M →
      (∫ t, |iteratedDeriv 5 (cutoffMultiplier M) t|) ≤ C / M := by
  obtain ⟨A, B, hA, hB, hb⟩ := multiplier_deriv_bounds
  refine ⟨2 * (A + B), by positivity, fun M hM => ?_⟩
  have hMp : 0 < M := by linarith
  have hd := width_pos hMp
  let D : ℝ → ℝ := fun t => |iteratedDeriv 5 (cutoffMultiplier M) t|
  let g : ℝ → ℝ := (Icc 0 M).indicator (fun _ => A * M⁻¹ ^ 5) +
    (Icc M (M + cutoffWidth M)).indicator (fun _ => B * (cutoffWidth M)⁻¹ ^ 5)
  have hi : Integrable D := multiplier_deriv_integrable hMp 5
  have hg₁ : Integrable ((Icc 0 M).indicator (fun _ : ℝ => A * M⁻¹ ^ 5)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have hg₂ : Integrable ((Icc M (M + cutoffWidth M)).indicator
      (fun _ : ℝ => B * (cutoffWidth M)⁻¹ ^ 5)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have hg : Integrable g := hg₁.add hg₂
  have hgn (t : ℝ) : 0 ≤ g t := by
    apply add_nonneg <;> apply Set.indicator_nonneg <;> intro x hx <;> positivity
  have hdom (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : D t ≤ g t := by
    have ht0 : 0 ≤ t := le_of_lt ht
    by_cases htc : t < M
    · have hmem : t ∈ Icc (0 : ℝ) M := ⟨ht0, htc.le⟩
      have hno : t ∉ Icc M (M + cutoffWidth M) := fun hx => (not_le_of_gt htc) hx.1
      simpa [g, hmem, hno] using (hb M hM t ht0).1 htc
    · by_cases htb : t ≤ M + cutoffWidth M
      · have hmem : t ∈ Icc M (M + cutoffWidth M) := ⟨le_of_not_gt htc, htb⟩
        have hbnd := (hb M hM t ht0).2 htb
        have hz : 0 ≤ (Icc 0 M).indicator (fun _ : ℝ => A * M⁻¹ ^ 5) t := by
          apply Set.indicator_nonneg; intro x hx; positivity
        simpa only [g, Pi.add_apply, indicator_of_mem hmem] using
          hbnd.trans (le_add_of_nonneg_left hz)
      · have hz := multiplier_deriv_zero hMp (t := t)
          (by simpa [abs_of_nonneg ht0] using lt_of_not_ge htb)
        simpa only [D, hz, abs_zero] using hgn t
  have he : (∫ t, D t) = 2 * ∫ t in Ioi (0 : ℝ), D t := by
    have hfun : (fun t => D |t|) = D := funext (multiplier_deriv_abs M)
    calc (∫ t, D t) = ∫ t, D |t| := congrArg (fun f : ℝ → ℝ => ∫ t, f t) hfun.symm
         _ = _ := integral_comp_abs
  rw [he]
  have hi_le : (∫ t in Ioi (0 : ℝ), D t) ≤ ∫ t, g t :=
    (setIntegral_mono_on hi.integrableOn hg.integrableOn measurableSet_Ioi hdom).trans
      (setIntegral_le_integral hg (Filter.Eventually.of_forall hgn))
  have hgint : (∫ t, g t) = A * M⁻¹ ^ 4 + B * (cutoffWidth M)⁻¹ ^ 4 := by
    simp only [g, Pi.add_apply]
    rw [integral_add hg₁ hg₂]
    simp only [integral_indicator_const _ measurableSet_Icc,
      Real.volume_real_Icc_of_le (show 0 ≤ M by linarith),
      Real.volume_real_Icc_of_le (show M ≤ M + cutoffWidth M by linarith), smul_eq_mul]
    simp only [sub_zero, add_sub_cancel_left]
    field_simp
  have hM4 : M⁻¹ ^ 4 ≤ M⁻¹ := by
    have h0 : 0 ≤ M⁻¹ := inv_nonneg.mpr hMp.le
    have h1 : M⁻¹ ≤ 1 := (inv_le_one₀ hMp).2 hM
    calc M⁻¹ ^ 4 ≤ M⁻¹ ^ 1 := pow_le_pow_of_le_one h0 h1 (by omega)
         _ = _ := pow_one _
  have hd4 : (cutoffWidth M)⁻¹ ^ 4 = M⁻¹ := by rw [inv_pow, width_fourth hMp]
  rw [hgint, hd4] at hi_le
  calc 2 * ∫ t in Ioi (0 : ℝ), D t ≤ 2 * (A * M⁻¹ ^ 4 + B * M⁻¹) := by linarith
       _ ≤ 2 * (A + B) / M := by
         rw [div_eq_mul_inv]
         nlinarith [mul_le_mul_of_nonneg_left hM4 hA.le]

private lemma kernel_representation {M : ℝ} (hM : 0 < M) (v : ℝ) :
    cutoffKernelSchwartz M v = (2 * Real.pi)⁻¹ •
      𝓕 (multiplierSchwartzPos M hM) (-v / (2 * Real.pi)) := by
  let F : ℝ → ℂ := fun t => Complex.exp ((↑(t * v) : ℂ) * Complex.I) *
    (cutoffMultiplier M t : ℂ)
  have hleft : cutoffKernelSchwartz M v = ∫ ξ, F (2 * Real.pi * ξ) := by
    change 𝓕⁻ (cutoffMultiplierSchwartz M) v = _
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards [] with ξ
    rw [multiplierSchwartz_apply hM]
    simp [F, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  have hright : 𝓕 (multiplierSchwartzPos M hM) (-v / (2 * Real.pi)) = ∫ t, F t := by
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards [] with t
    have ha : -2 * Real.pi * t * (-v / (2 * Real.pi)) = t * v := by field_simp
    change Complex.exp ((↑(-2 * Real.pi * t * (-v / (2 * Real.pi))) : ℂ) * Complex.I) *
      (cutoffMultiplier M t : ℂ) = F t
    rw [ha]
  rw [hleft, hright, Measure.integral_comp_mul_left,
    abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹)]

private lemma complex_deriv_norm {M : ℝ} (hM : 0 < M) (n : ℕ) (t : ℝ) :
    ‖iteratedDeriv n (multiplierSchwartzPos M hM : ℝ → ℂ) t‖ =
      |iteratedDeriv n (cutoffMultiplier M) t| := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖iteratedFDeriv ℝ n (Complex.ofRealLI ∘ cutoffMultiplier M) t‖ = _
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left
    ((cutoff_multiplier_contDiff M).of_le
      (show (n : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt
    le_rfl, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]

private lemma kernel_decay {M : ℝ} (hM : 0 < M) (v : ℝ) :
    |v| ^ 5 * |cutoffKernel M v| ≤ (2 * Real.pi)⁻¹ *
      ∫ t, |iteratedDeriv 5 (cutoffMultiplier M) t| := by
  let f := multiplierSchwartzPos M hM
  have hi (n : ℕ) : Integrable (iteratedDeriv n (f : ℝ → ℂ)) := by
    apply (integrable_norm_iff
      ((f.smooth (n + 1)).differentiable_iteratedDeriv' n).continuous.aestronglyMeasurable).mp
    change Integrable (fun t => ‖iteratedDeriv n (multiplierSchwartzPos M hM : ℝ → ℂ) t‖)
    simpa only [complex_deriv_norm hM] using multiplier_deriv_integrable hM n
  have hd := congrFun (Real.fourier_iteratedDeriv (f.smooth 5) (fun n hn => hi n)
    (show (5 : ℕ∞) ≤ 5 from le_rfl)) (-v / (2 * Real.pi))
  have hb := Real.norm_fourier_le_integral_norm (iteratedDeriv 5 (f : ℝ → ℂ)) (-v / (2 * Real.pi))
  rw [hd] at hb
  have hnorm : ‖(2 * Real.pi * Complex.I * (↑(-v / (2 * Real.pi)) : ℂ)) ^ 5‖ = |v| ^ 5 := by
    have he : 2 * Real.pi * Complex.I * (↑(-v / (2 * Real.pi)) : ℂ) = -(v : ℂ) * Complex.I := by
      push_cast
      field_simp
    rw [he]
    simp [norm_pow]
  simp only [norm_smul, hnorm] at hb
  dsimp only [f] at hb
  simp only [complex_deriv_norm hM] at hb
  have hk := congrArg norm (kernel_representation hM v)
  rw [cutoff_kernelSchwartz_coe] at hk
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹)] at hk
  rw [SchwartzMap.fourier_coe] at hk
  rw [hk]
  nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]

theorem cutoff_kernel_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 1 ≤ M →
      (∫ v in {v : ℝ | 1 ≤ |v|}, |cutoffKernel M v|) ≤ C / M := by
  obtain ⟨D, hD, hb⟩ := multiplier_derivative_budget
  let w : ℝ → ℝ := fun v => (1 + |v|)⁻¹ ^ 5
  have hwn (v : ℝ) : 0 ≤ w v := by dsimp [w]; positivity
  have hw : Integrable w := by
    have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 5) (by norm_num)
    refine h.congr (Filter.Eventually.of_forall (fun v => ?_))
    dsimp [w]
    rw [Real.rpow_neg_eq_inv_rpow]
    exact Real.rpow_natCast _ 5
  have hW : 0 ≤ ∫ v, w v := integral_nonneg hwn
  refine ⟨32 * (2 * Real.pi)⁻¹ * D * ((∫ v, w v) + 1), by positivity,
    fun M hM => ?_⟩
  have hMp : 0 < M := by linarith
  have hpoint (v : ℝ) (hv : 1 ≤ |v|) :
      |cutoffKernel M v| ≤ (32 * (2 * Real.pi)⁻¹ * D / M) * w v := by
    have hk : |v| ^ 5 * |cutoffKernel M v| ≤ (2 * Real.pi)⁻¹ * D / M := by
      calc _ ≤ (2 * Real.pi)⁻¹ * ∫ t, |iteratedDeriv 5 (cutoffMultiplier M) t| :=
             kernel_decay hMp v
           _ ≤ (2 * Real.pi)⁻¹ * (D / M) := by gcongr; exact hb M hM
           _ = _ := by ring
    have hp : (1 + |v|) ^ 5 ≤ 32 * |v| ^ 5 := by
      calc _ ≤ (2 * |v|) ^ 5 := pow_le_pow_left₀ (by positivity) (by linarith) 5
           _ = _ := by ring
    change |cutoffKernel M v| ≤ (32 * (2 * Real.pi)⁻¹ * D / M) * (1 + |v|)⁻¹ ^ 5
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < (1 + |v|) ^ 5)]
    calc _ ≤ |cutoffKernel M v| * (32 * |v| ^ 5) :=
           mul_le_mul_of_nonneg_left hp (abs_nonneg _)
         _ = 32 * (|v| ^ 5 * |cutoffKernel M v|) := by ring
         _ ≤ 32 * ((2 * Real.pi)⁻¹ * D / M) := by linarith
         _ = _ := by ring
  have hi : Integrable (fun v => |cutoffKernel M v|) := (cutoff_kernel_integrable M).norm
  have hc : 0 ≤ 32 * (2 * Real.pi)⁻¹ * D / M := by positivity
  calc
    _ ≤ ∫ v in {v : ℝ | 1 ≤ |v|}, (32 * (2 * Real.pi)⁻¹ * D / M) * w v :=
      setIntegral_mono_on hi.integrableOn (hw.const_mul _).integrableOn
        (isClosed_le continuous_const continuous_abs).measurableSet hpoint
    _ ≤ ∫ v, (32 * (2 * Real.pi)⁻¹ * D / M) * w v :=
      setIntegral_le_integral (hw.const_mul _) (Filter.Eventually.of_forall
        (fun v => mul_nonneg hc (hwn v)))
    _ = (32 * (2 * Real.pi)⁻¹ * D / M) * ∫ v, w v := integral_const_mul _ _
    _ ≤ 32 * (2 * Real.pi)⁻¹ * D * ((∫ v, w v) + 1) / M := by
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff_of_pos_right hMp).2
      nlinarith [show 0 < 32 * (2 * Real.pi)⁻¹ * D by positivity]

end
end D5.S3.Analytic.Fourier.GaussianCutoff
