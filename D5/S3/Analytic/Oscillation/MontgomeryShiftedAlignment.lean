/- GID: D5/S3/Analytic/Oscillation/MontgomeryShiftedAlignment
   generality: I
   mirror-B: D5/B/S3/Analytic/Oscillation/MontgomeryShiftedAlignment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A shifted commensurate return separates phase cancellation from Lorentz pair energy. -/

import D5.S3.Analytic.Asymptotics.DirichletPolynomialMeanSquare
import D5.S3.Analytic.Oscillation.SpectrumTwoTermCountAlignment
import D5.S3.Analytic.Oscillation.MontgomeryAlignmentLower
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import D5.S3.Analytic.Oscillation.MontgomeryCountUpper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import OmegaBuild.Commands

/-! Phase cancellation and Lorentz pair energy at the same shifted frequency. -/

compile_only_with_mathlib

namespace D5.S3.Analytic.Oscillation.MontgomeryShiftedAlignment

open OrdinateCounting MontgomeryCountUpper MontgomeryWindow
open scoped BigOperators

noncomputable section

private lemma cosine_weight_loss (d h : ℝ) :
    0 ≤ (4 / (4 + d ^ 2)) * (1 - Real.cos (d * h)) ∧
    (4 / (4 + d ^ 2)) * (1 - Real.cos (d * h)) ≤ 2 * h ^ 2 := by
  have hden : 0 < 4 + d ^ 2 := by positivity
  constructor
  · exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one _))
  · have hcos : 1 - Real.cos (d * h) ≤ (d * h) ^ 2 / 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := d * h)]
    calc
      _ ≤ (4 / (4 + d ^ 2)) * ((d * h) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hcos (by positivity)
      _ = (2 * h ^ 2) * (d ^ 2 / (4 + d ^ 2)) := by
        field_simp
        ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity)
        ((div_le_one hden).mpr (by linarith))

/-- At an aligned phase the Lorentz pair sum loses at most a quadratic amount under a shift. -/
theorem pairSum_loss_of_aligned_shift (S : Spectrum) (Y p h : ℝ)
    (halign : ∀ j ∈ S.cut Y, ∀ k ∈ S.cut Y, Real.cos ((S.gamma j - S.gamma k) * p) = 1) :
    0 ≤ pairSum S Y p - pairSum S Y (p + h) ∧
    pairSum S Y p - pairSum S Y (p + h) ≤ 2 * h ^ 2 * (S.N Y : ℝ) ^ 2 := by
  have hpair (j : S.index) (hj : j ∈ S.cut Y) (k : S.index) (hk : k ∈ S.cut Y) :
      let d := S.gamma j - S.gamma k
      pairCos d p - pairCos d (p + h) = (4 / (4 + d ^ 2)) * (1 - Real.cos (d * h)) := by
    dsimp
    have hc := halign j hj k hk
    have hs : Real.sin ((S.gamma j - S.gamma k) * p) = 0 := by
      have hs := Real.sin_sq_add_cos_sq ((S.gamma j - S.gamma k) * p)
      rw [hc] at hs
      nlinarith
    rw [pairCos, pairCos, mul_add, Real.cos_add, hc, hs]
    ring
  have hsum :
      pairSum S Y p - pairSum S Y (p + h) =
        ∑ j ∈ S.cut Y, ∑ k ∈ S.cut Y, (S.mult j : ℝ) * (S.mult k : ℝ) *
          (pairCos (S.gamma j - S.gamma k) p - pairCos (S.gamma j - S.gamma k) (p + h)) := by
    unfold pairSum
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hsum]
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    apply Finset.sum_nonneg
    intro k hk
    rw [hpair j hj k hk]
    exact mul_nonneg (by positivity) (cosine_weight_loss _ _).1
  · calc
      _ ≤ ∑ j ∈ S.cut Y, ∑ k ∈ S.cut Y, (S.mult j : ℝ) * (S.mult k : ℝ) * (2 * h ^ 2) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        rw [hpair j hj k hk]
        exact mul_le_mul_of_nonneg_left (cosine_weight_loss _ _).2 (by positivity)
      _ = (∑ j ∈ S.cut Y, (S.mult j : ℝ)) *
          ((∑ k ∈ S.cut Y, (S.mult k : ℝ)) * (2 * h ^ 2)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = _ := by rw [Spectrum.N, Nat.cast_sum]; ring

open Set Filter MeasureTheory
open scoped Topology

private theorem count_integral_sub (S : Spectrum) {Y : ℝ} (hY : 0 < Y)
    {f f' : ℝ → ℂ} (hf : ∀ u, HasDerivAt f (f' u) u) (hf' : Continuous f') :
    (∑ j ∈ S.cut Y, (S.mult j : ℂ) * f (S.gamma j / Y)) =
      (S.N Y : ℂ) * f 1 - ∫ u in Ioc (0 : ℝ) 1, (S.N (Y * u) : ℂ) * f' u := by
  classical
  let k (j : S.index) : ℝ → ℂ :=
    (Icc (S.gamma j / Y) 1).indicator (fun u => (S.mult j : ℂ) * f' u)
  have hInt (j : S.index) : IntegrableOn (k j) (Ioc (0 : ℝ) 1) :=
    ((continuous_const.mul hf').integrableOn_Ioc).indicator measurableSet_Icc
  have hEach (j : S.index) (hj : j ∈ S.cut Y) :
      (∫ u in Ioc (0 : ℝ) 1, k j u) =
        (S.mult j : ℂ) * (f 1 - f (S.gamma j / Y)) := by
    have hjY : S.gamma j ≤ Y := by simpa [Spectrum.cut] using hj
    have hlow : 0 < S.gamma j / Y := div_pos (S.gamma_pos j) hY
    have hle : S.gamma j / Y ≤ 1 := (div_le_one hY).mpr hjY
    have hsub : Icc (S.gamma j / Y) 1 ⊆ Ioc (0 : ℝ) 1 :=
      fun _ hx => ⟨hlow.trans_le hx.1, hx.2⟩
    dsimp only [k]
    rw [setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr hsub,
      integral_Icc_eq_integral_Ioc, integral_const_mul, ← intervalIntegral.integral_of_le hle]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x)
      (hf'.intervalIntegrable _ _)]
  have hsum (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) 1) :
      (S.N (Y * u) : ℂ) * f' u = ∑ j ∈ S.cut Y, k j u := by
    have hsub : S.cut (Y * u) ⊆ S.cut Y := by
      intro j hj
      have hj' : S.gamma j ≤ Y * u := by simpa [Spectrum.cut] using hj
      have hYu : Y * u ≤ Y := by nlinarith [hu.2]
      simpa [Spectrum.cut] using hj'.trans hYu
    rw [Spectrum.N, Nat.cast_sum, Finset.sum_mul, ← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro j hj
      have hj' : S.gamma j ≤ Y * u := by simpa [Spectrum.cut] using hj
      have hle := (div_le_iff₀ hY).mpr (by simpa [mul_comm] using hj')
      exact (indicator_of_mem (show u ∈ Icc (S.gamma j / Y) 1 from ⟨hle, hu.2⟩)
        (fun x => (S.mult j : ℂ) * f' x)).symm
    · intro j _ hj
      apply indicator_of_notMem
      intro hu'
      apply hj
      have hju := (div_le_iff₀ hY).mp (show S.gamma j / Y ≤ u from hu'.1)
      simpa [Spectrum.cut, mul_comm] using hju
  rw [setIntegral_congr_fun measurableSet_Ioc hsum, integral_finsetSum _ (fun j _ => hInt j),
    Finset.sum_congr rfl hEach]
  rw [Spectrum.N, Nat.cast_sum, Finset.sum_mul]
  simp only [mul_sub, Finset.sum_sub_distrib]
  abel

private theorem scaled_count_test_limit (S : Spectrum) (hN : CountAsymptotic S)
    {f f' : ℝ → ℂ} (hf : ∀ u, HasDerivAt f (f' u) u) (hf' : Continuous f') :
    Tendsto (fun Y : ℝ =>
      (∑ j ∈ S.cut Y, (S.mult j : ℂ) * f (S.gamma j / Y)) /
        ((Y * Real.log Y : ℝ) : ℂ))
      atTop (𝓝 ((1 / (2 * (Real.pi : ℂ))) * ∫ u in (0 : ℝ)..1, f u)) := by
  let c : ℝ := 1 / (2 * Real.pi)
  let F : ℝ → ℝ → ℝ := fun Y u => (S.N (Y * u) : ℝ) / (Y * Real.log Y)
  have hcompact : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc
  obtain ⟨K, hK⟩ := hcompact.exists_bound_of_continuousOn hf'.continuousOn
  have hmeas (Y : ℝ) : Measurable (F Y) :=
    ((count_mono S).measurable.comp (measurable_const.mul measurable_id)).div_const _
  have hbound : ∀ᶠ Y : ℝ in atTop,
      ∀ᵐ u ∂volume.restrict (Ioc (0 : ℝ) 1), ‖(F Y u : ℂ) * f' u‖ ≤ (c + 1) * K := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), hN.eventually (gt_mem_nhds (show c < c + 1 by linarith))]
      with Y hY hNY
    apply (ae_restrict_mem measurableSet_Ioc).mono
    intro u hu
    have hden : 0 < Y * Real.log Y := mul_pos (by linarith) (Real.log_pos (by linarith))
    have hFY : F Y u ≤ c + 1 :=
      (div_le_div_of_nonneg_right (count_mono S (by nlinarith [hu.2])) hden.le).trans hNY.le
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by dsimp [F]; positivity)]
    exact mul_le_mul hFY (hK u ⟨hu.1.le, hu.2⟩) (norm_nonneg _) (by dsimp [c]; positivity)
  have hlim : ∀ᵐ u ∂volume.restrict (Ioc (0 : ℝ) 1),
      Tendsto (fun Y => (F Y u : ℂ) * f' u) atTop (𝓝 ((c * u : ℝ) * f' u)) := by
    apply (ae_restrict_mem measurableSet_Ioc).mono
    intro u hu
    exact ((Complex.continuous_ofReal.tendsto _).comp (count_scaled_limit S hN hu.1)).mul_const _
  have hmeasure (Y : ℝ) : AEStronglyMeasurable (fun u => (F Y u : ℂ) * f' u)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((Complex.continuous_ofReal.measurable.comp (hmeas Y)).mul hf'.measurable).aestronglyMeasurable
  have hconv := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (fun _ => (c + 1) * K) (.of_forall hmeasure) hbound (integrableOn_const (C := (c + 1) * K) (by simp)) hlim
  have hV := (((Complex.continuous_ofReal.tendsto c).comp hN).mul_const (f 1)).sub hconv
  have hfC : Continuous f := continuous_iff_continuousAt.mpr fun u => (hf u).continuousAt
  have hProd (u : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ) * f x)
      (f u + (u : ℂ) * f' u) u := by
    have hu : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 u :=
      Complex.ofRealCLM.hasDerivAt
    convert hu.mul (hf u) using 1
    · ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun x _ => hProd x)
    ((hfC.add (Complex.continuous_ofReal.mul hf')).intervalIntegrable _ _)
  have hfi : IntervalIntegrable f volume 0 1 := hfC.intervalIntegrable _ _
  have hdiff : IntervalIntegrable (fun u : ℝ => (u : ℂ) * f' u) volume 0 1 :=
    (Complex.continuous_ofReal.mul hf').intervalIntegrable _ _
  rw [intervalIntegral.integral_add hfi hdiff] at hFTC
  have hEq :
      (c : ℂ) * f 1 - (∫ u in Ioc (0 : ℝ) 1, (c * u : ℝ) * f' u) =
        (1 / (2 * (Real.pi : ℂ))) * ∫ u in (0 : ℝ)..1, f u := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [Complex.ofReal_mul, mul_assoc, intervalIntegral.integral_const_mul,
      Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, sub_zero] at hFTC ⊢
    have hc : (c : ℂ) = 1 / (2 * (Real.pi : ℂ)) := by dsimp [c]; push_cast; ring
    rw [← hc, ← mul_sub, ← hFTC]
    ring
  rw [← hEq]
  refine hV.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
  change (((S.N Y : ℝ) / (Y * Real.log Y) : ℝ) : ℂ) * f 1 -
      (∫ u in Ioc (0 : ℝ) 1, (F Y u : ℂ) * f' u) = _
  rw [count_integral_sub S (zero_lt_one.trans hY) hf hf', sub_div, ← integral_div]
  congr 1
  · push_cast
    ring
  · apply integral_congr_ae
    filter_upwards with u
    dsimp [F]
    push_cast
    ring

open D5.S3.Weil.DirichletPolynomialMeanSquare (phase)

private theorem sin_eq_one_of_sine_eq_mass (S : Spectrum) {w : S.index → ℝ}
    (hw : ∀ j, 0 < w j) {Y p : ℝ}
    (hp : SpectrumPhaseCutoff.sine S w Y p = SpectrumPhaseCutoff.mass S w Y) :
    ∀ j ∈ S.cut Y, Real.sin (S.gamma j * p) = 1 := by
  have hsum : (∑ j ∈ S.cut Y, w j * (1 - Real.sin (S.gamma j * p))) = 0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hp.symm
  have hn (j : S.index) (_ : j ∈ S.cut Y) :
      0 ≤ w j * (1 - Real.sin (S.gamma j * p)) :=
    mul_nonneg (hw j).le (sub_nonneg.mpr (Real.sin_le_one _))
  intro j hj
  have h := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hsum j hj
  exact (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (hw j).ne')).symm

private theorem phase_eq_I_of_sin_eq_one {v p : ℝ} (hp : Real.sin (v * p) = 1) :
    phase v p = Complex.I := by
  have hc : Real.cos (v * p) = 0 := by
    have h := Real.sin_sq_add_cos_sq (v * p)
    rw [hp] at h
    nlinarith
  unfold phase
  rw [show (v : ℂ) * Complex.I * (p : ℂ) = ↑(v * p) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hp, hc]
  simp

private theorem phase_shift_sum (S : Spectrum) {Y p h : ℝ}
    (hp : ∀ j ∈ S.cut Y, Real.sin (S.gamma j * p) = 1) :
    (∑ j ∈ S.cut Y, (S.mult j : ℂ) * phase (S.gamma j) (p + h)) =
      Complex.I * ∑ j ∈ S.cut Y, (S.mult j : ℂ) * phase (S.gamma j) h := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he : phase (S.gamma j) (p + h) =
      phase (S.gamma j) p * phase (S.gamma j) h := by
    simp only [phase, Complex.ofReal_add, mul_add, Complex.exp_add]
  rw [he, phase_eq_I_of_sin_eq_one (hp j hj)]
  ring

private theorem phase_at_inverse_height_limit (S : Spectrum) (hN : CountAsymptotic S) :
    Tendsto (fun Y : ℝ => (∑ j ∈ S.cut Y, (S.mult j : ℂ) *
      phase (S.gamma j) (2 * Real.pi / Y)) / ((Y * Real.log Y : ℝ) : ℂ)) atTop (𝓝 0) := by
  let a : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  let f : ℝ → ℂ := fun u => Complex.exp (a * (u : ℂ))
  let f' : ℝ → ℂ := fun u => a * f u
  have ha : a ≠ 0 := by dsimp [a]; exact mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hf (u : ℝ) : HasDerivAt f (f' u) u := by
    have hu : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    simpa [f, f', mul_comm] using (hu.const_mul a).cexp
  have hf' : Continuous f' := by unfold f' f; fun_prop
  have hi : (∫ u in (0 : ℝ)..1, f u) = 0 := by
    rw [show f = (fun u : ℝ => Complex.exp (a * (u : ℂ))) from rfl,
      integral_exp_mul_complex ha]
    simp [a, Complex.exp_two_pi_mul_I]
  have h := scaled_count_test_limit S hN hf hf'
  rw [hi, mul_zero] at h
  apply h.congr
  intro Y
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  unfold f phase a
  push_cast
  congr 1
  ring

private abbrev countCoefficient : ℝ := 1 / (2 * Real.pi)

private abbrev resonanceCoefficient : ℝ := 2 * Real.pi * countCoefficient ^ 2

private theorem loss_scale_limit (S : Spectrum) (hN : CountAsymptotic S) :
    Tendsto (fun Y : ℝ => 2 * (2 * Real.pi / Y) ^ 2 * (S.N Y : ℝ) ^ 2 /
      (Y * Real.log Y ^ 2)) atTop (𝓝 0) := by
  have h := ((hN.pow 2).const_mul (2 * (2 * Real.pi) ^ 2)).div_atTop
    (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
  have hY0 := zero_lt_one.trans hY
  have hlog := Real.log_pos hY
  dsimp only [id_eq]
  field_simp [hY0.ne', hlog.ne']

private theorem aligned_shift_limit (S : Spectrum) {D : ℝ}
    (hcount : ∀ᶠ Y : ℝ in atTop, |(S.N Y : ℝ) -
      Y / (2 * Real.pi) * (Real.log (Y / (2 * Real.pi)) - 1)| ≤ D)
    (p : ℝ → ℝ)
    (hp : ∀ᶠ Y : ℝ in atTop, ∀ j ∈ S.cut Y, Real.sin (S.gamma j * p Y) = 1) :
    Tendsto (fun Y : ℝ => pairSum S Y (p Y + 2 * Real.pi / Y) /
      (Y * Real.log Y ^ 2)) atTop (𝓝 resonanceCoefficient) := by
  have hcnt : ∀ᶠ Y : ℝ in atTop, |(S.N Y : ℝ) -
    SmoothedSpectrumCounting.CutDensity.countMain (2 * Real.pi) Y| ≤ D := by
    simpa only [SmoothedSpectrumCounting.CutDensity.countMain, div_mul_eq_mul_div] using hcount
  have hN := count_asymptotic_of_bounded_discrepancy S hcnt
  have h0 := loss_scale_limit S hN
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let ε := (resonanceCoefficient - a) / 3
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hκ : a + 2 * ε < resonanceCoefficient := by dsimp [ε]; linarith
    have hlow := MontgomeryAlignmentLower.eventually_montgomery_gt_of_phase_alignment S hN hκ
    filter_upwards [eventually_gt_atTop (1 : ℝ), hp, hlow,
      h0.eventually (gt_mem_nhds hε)] with Y hY hsin hl herr
    have hpairs (j : S.index) (hj : j ∈ S.cut Y) (k : S.index) (hk : k ∈ S.cut Y) :
        Real.cos ((S.gamma j - S.gamma k) * p Y) = 1 := by
      have hcos (i : S.index) (hi : i ∈ S.cut Y) : Real.cos (S.gamma i * p Y) = 0 := by
        have hs := Real.sin_sq_add_cos_sq (S.gamma i * p Y)
        rw [hsin i hi] at hs
        nlinarith
      rw [sub_mul, Real.cos_sub, hsin j hj, hsin k hk, hcos j hj, hcos k hk]
      norm_num
    have hL := hl (p Y) hpairs
    rw [← montgomery_normalization S hY] at hL
    change (a + 2 * ε) * (Y * Real.log Y ^ 2) < pairSum S Y (p Y) at hL
    have hshift := (pairSum_loss_of_aligned_shift S Y (p Y) (2 * Real.pi / Y) hpairs).2
    have hden : 0 < Y * Real.log Y ^ 2 :=
      mul_pos (zero_lt_one.trans hY) (pow_pos (Real.log_pos hY) 2)
    rw [div_lt_iff₀ hden] at herr
    apply (lt_div_iff₀ hden).mpr
    nlinarith [mul_pos hε hden]
  · intro b hb
    let ε := (b - resonanceCoefficient) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      pairSum_le_of_bounded_discrepancy S hcnt hε] with Y hY hu
    have hden : 0 < Y * Real.log Y ^ 2 :=
      mul_pos (zero_lt_one.trans hY) (pow_pos (Real.log_pos hY) 2)
    apply (div_lt_iff₀ hden).mpr
    apply (hu _).trans_lt
    apply mul_lt_mul_of_pos_right _ hden
    change resonanceCoefficient + ε < b
    dsimp [ε]
    linarith

private theorem shifted_phase_norm_limit (S : Spectrum) (hN : CountAsymptotic S) (p : ℝ → ℝ)
    (hp : ∀ᶠ Y : ℝ in atTop, ∀ j ∈ S.cut Y, Real.sin (S.gamma j * p Y) = 1) :
    Tendsto (fun Y : ℝ => ‖∑ j ∈ S.cut Y, (S.mult j : ℂ) *
      phase (S.gamma j) (p Y + 2 * Real.pi / Y)‖ / (S.N Y : ℝ)) atTop (𝓝 0) := by
  have hc : 0 < countCoefficient := by dsimp [countCoefficient]; positivity
  have hf := (phase_at_inverse_height_limit S hN).norm.div hN hc.ne'
  simp only [norm_zero, zero_div] at hf
  apply hf.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ), hp] with Y hY hpY
  have hpos := mul_pos (zero_lt_one.trans hY) (Real.log_pos hY)
  change (‖(∑ j ∈ S.cut Y, (S.mult j : ℂ) * phase (S.gamma j) (2 * Real.pi / Y)) /
      ((Y * Real.log Y : ℝ) : ℂ)‖) / ((S.N Y : ℝ) / (Y * Real.log Y)) = _
  rw [phase_shift_sum S hpY, norm_mul, Complex.norm_I, one_mul, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  exact div_div_div_cancel_right₀ hpos.ne' _ _

/-- One spectrum attains the Lorentz leading coefficient while its normalized phase score tends to zero. -/
theorem exists_commensurate_shift_with_phase_cancellation :
    ∃ (S : Spectrum) (p : ℝ → ℝ) (B : ℝ), 1 < B ∧
      (∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ Y : ℝ in atTop, |(S.N Y : ℝ) -
        Y / (2 * Real.pi) * (Real.log (Y / (2 * Real.pi)) - 1)| ≤ D) ∧
      (∀ᶠ Y : ℝ in atTop,
        Real.log Y ≤ p Y ∧ p Y + 2 * Real.pi / Y ≤ B * Real.log Y ∧
        ∀ j ∈ S.cut Y, Real.sin (S.gamma j * p Y) = 1) ∧
      Tendsto (fun Y : ℝ => ‖∑ j ∈ S.cut Y, (S.mult j : ℂ) *
        phase (S.gamma j) (p Y + 2 * Real.pi / Y)‖ / (S.N Y : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun Y : ℝ => pairSum S Y (p Y + 2 * Real.pi / Y) /
        (Y * Real.log Y ^ 2)) atTop (𝓝 (2 * Real.pi * (1 / (2 * Real.pi)) ^ 2)) := by
  classical
  obtain ⟨S, w, _, hw, ⟨D, hD, hcount⟩, _, _, hprog⟩ :=
    SpectrumTwoTermCountAlignment.exists_two_term_count_alignment
  let L : ℝ := 42 * Real.pi / Real.log 2
  let B : ℝ := 2 * L + 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hB : 1 < B := by dsimp [B]; linarith
  have hsmall : ∀ᶠ Y : ℝ in atTop, 2 * Real.pi / Y ≤ Real.log Y := by
    filter_upwards [(tendsto_const_nhds.div_atTop
      (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)).eventually
        (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num) : Set.Iio 1 ∈ 𝓝 (0 : ℝ)),
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with Y hdiv hlog
    exact (show 2 * Real.pi / Y < 1 from hdiv).le.trans hlog
  have hex : ∀ᶠ Y : ℝ in atTop, ∃ p : ℝ,
      Real.log Y ≤ p ∧ p + 2 * Real.pi / Y ≤ B * Real.log Y ∧
      ∀ j ∈ S.cut Y, Real.sin (S.gamma j * p) = 1 := by
    filter_upwards [hprog, hsmall, eventually_ge_atTop (21 : ℝ)] with Y hY hshift hlarge
    obtain ⟨_, q, _, _, hs, hvisit⟩ := hY
    obtain ⟨m, hm⟩ := hvisit (Real.log Y)
    have hl : Real.log (21 * Y) ≤ 2 * Real.log Y := by
      rw [Real.log_mul (by norm_num) (by linarith : Y ≠ 0)]
      linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 21) hlarge]
    refine ⟨_, hm.1.le, ?_, sin_eq_one_of_sine_eq_mass S (fun j => ?_) (hs m Y le_rfl)⟩
    · have hupper := hm.2
      change _ < Real.log Y + L * Real.log (21 * Y) at hupper
      dsimp [B]
      linarith [mul_le_mul_of_nonneg_left hl hL.le]
    · rw [(hw j).2]
      exact div_pos (S.gamma_pos j) (by positivity)
  let good (Y t : ℝ) := Real.log Y ≤ t ∧ t + 2 * Real.pi / Y ≤ B * Real.log Y ∧
    ∀ j ∈ S.cut Y, Real.sin (S.gamma j * t) = 1
  let p (Y : ℝ) := if h : ∃ t, good Y t then h.choose else 0
  have hp : ∀ᶠ Y : ℝ in atTop, good Y (p Y) := by
    filter_upwards [hex] with Y h
    change good Y (if h' : ∃ t, good Y t then h'.choose else 0)
    rw [dite_eq_left h]
    exact h.choose_spec
  have hsin := hp.mono (fun _ h => h.2.2)
  exact ⟨S, p, B, hB, ⟨D, hD, hcount⟩, hp,
    shifted_phase_norm_limit S (count_asymptotic_of_bounded_discrepancy S (by
      simpa only [SmoothedSpectrumCounting.CutDensity.countMain, div_mul_eq_mul_div] using hcount)) p hsin,
    aligned_shift_limit S hcount p hsin⟩

#print axioms exists_commensurate_shift_with_phase_cancellation

end

end D5.S3.Analytic.Oscillation.MontgomeryShiftedAlignment
