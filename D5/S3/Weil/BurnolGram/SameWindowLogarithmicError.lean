/- GID: D5/S3/Weil/BurnolGram/SameWindowLogarithmicError
   generality: I
   mirror-B: D5/B/S3/Weil/BurnolGram/SameWindowLogarithmicError
   mirror-E: none(waiver:analytic-same-window-logarithmic-error)
   anchors: []
   utility: none
   digest: Prove logarithmic Fourier convergence of the same-window error. -/

import D5.S3.Weil.BurnolGram.SameWindowFourierDecay
import D5.S3.Analytic.Fourier.LogarithmicTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Group.Integral

/-!
# Logarithmic Fourier convergence of the actual same-window error

The Fourier transform is taken at angular frequency, with the repository's
kernel exp(-itx). The norm has factor 1/(2*pi). Actual low- and high-frequency
bounds dominate its nonnegative integrand by three integrable functions;
weighted integrability is proved before estimating its integral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.BurnolGram.SameWindowLogarithmicError

open Filter Set MeasureTheory
open D5.S3.Weil.Convention
open D5.S3.Weil.BurnolGram.SameWindowSmoothCutoff
open D5.S3.Weil.BurnolGram.SameWindowFourierDecay
open D5.S3.Analytic.Fourier.LogarithmicTail
open scoped Topology ContDiff

/-- The actual zero-extension error is transformed at angular frequency.
Its endpoint discontinuities are allowed; the input is not bundled as a test. -/
def sameWindowErrorFourier (a h : ℝ) (hh : 0 < h) (p : ℝ → ℂ)
    (hp : ContDiff ℝ ∞ p) (heven : ∀ x, p (-x) = p x) (t : ℝ) : ℂ :=
  ∫ x : ℝ, fourierKernel (t : ℂ) x *
    ((Ioo (-a) a).indicator p x - sameWindowSmoothTrial a h hh p hp heven x)

/-- The logarithmic Fourier error squared, with the angular factor 1/(2*pi).
The value at nonpositive widths only makes the right-limit function total. -/
def sameWindowLogarithmicError (a : ℝ) (p : ℝ → ℂ)
    (hp : ContDiff ℝ ∞ p) (heven : ∀ x, p (-x) = p x) (h : ℝ) : ℝ :=
  if hh : 0 < h then
    inverseFourierFactor *
      ∫ t : ℝ, (1 + Real.log (1 + |t|)) *
        ‖sameWindowErrorFourier a h hh p hp heven t‖ ^ 2
  else 0

private theorem angular_kernel_norm (t x : ℝ) :
    ‖fourierKernel (t : ℂ) x‖ = 1 := by
  simp [fourierKernel, Complex.norm_exp]

private theorem logarithmic_weight_nonneg (t : ℝ) :
    0 ≤ 1 + Real.log (1 + |t|) := by
  exact add_nonneg zero_le_one (Real.log_nonneg (by linarith [abs_nonneg t]))

private theorem continuous_logarithmic_weight :
    Continuous (fun t : ℝ => 1 + Real.log (1 + |t|)) := by
  have hbase : Continuous (fun t : ℝ => 1 + |t|) :=
    continuous_const.add continuous_abs
  exact continuous_const.add
    (hbase.log (fun t => by linarith [abs_nonneg t]))

/-- Both tails of the actual logarithmic majorant are integrable before
its comparison with the target integrand is used. -/
private theorem logarithmic_envelope (F : ℝ → ℂ) (hF : Continuous F)
    (A B R : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 < R)
    (hlow : ∀ t, ‖F t‖ ≤ A)
    (hhigh : ∀ t, t ≠ 0 → ‖F t‖ ≤ B / |t|) :
    Integrable (fun t : ℝ => (1 + Real.log (1 + |t|)) * ‖F t‖ ^ 2) ∧
      (∫ t : ℝ, (1 + Real.log (1 + |t|)) * ‖F t‖ ^ 2) ≤
        2 * A ^ 2 * R * (1 + Real.log (1 + R)) +
          2 * B ^ 2 * (2 + Real.log (1 + R)) / R := by
  let H : ℝ → ℝ := fun t => (1 + Real.log (1 + |t|)) * ‖F t‖ ^ 2
  let C : ℝ → ℝ := (Icc (-R) R).indicator
    (fun _ => A ^ 2 * (1 + Real.log (1 + R)))
  let P : ℝ → ℝ := (Ioi R).indicator
    (fun t => B ^ 2 * ((1 + Real.log (1 + t)) / t ^ 2))
  let G : ℝ → ℝ := fun t => C t + P t + P (-t)
  have hwR : 0 ≤ 1 + Real.log (1 + R) :=
    add_nonneg zero_le_one (Real.log_nonneg (by linarith))
  have hC : Integrable C :=
    (integrableOn_const (μ := volume) (s := Icc (-R) R)
      (C := A ^ 2 * (1 + Real.log (1 + R)))
      isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc
  have hPtail : IntegrableOn (fun t : ℝ =>
      B ^ 2 * ((1 + Real.log (1 + t)) / t ^ 2)) (Ioi R) :=
    (integrableOn_logarithmic_tail hR).const_mul (B ^ 2)
  have hP : Integrable P := hPtail.integrable_indicator measurableSet_Ioi
  have hPn : Integrable (fun t : ℝ => P (-t)) := hP.comp_neg
  have hCP : Integrable (fun t : ℝ => C t + P t) := hC.add hP
  have hG : Integrable G := hCP.add hPn
  have hC_nonneg (t : ℝ) : 0 ≤ C t := by
    by_cases ht : t ∈ Icc (-R) R
    · simpa only [C, indicator_of_mem ht] using mul_nonneg (sq_nonneg A) hwR
    · simp only [C, indicator_of_notMem ht, le_refl]
  have hP_nonneg (t : ℝ) : 0 ≤ P t := by
    by_cases ht : t ∈ Ioi R
    · have htpos : 0 < t := hR.trans ht
      have hw : 0 ≤ 1 + Real.log (1 + t) :=
        add_nonneg zero_le_one (Real.log_nonneg (by linarith))
      simpa only [P, indicator_of_mem ht] using
        mul_nonneg (sq_nonneg B) (div_nonneg hw (sq_nonneg t))
    · simp only [P, indicator_of_notMem ht, le_refl]
  have hdecay (t : ℝ) (ht : 0 < |t|) :
      H t ≤ B ^ 2 * ((1 + Real.log (1 + |t|)) / |t| ^ 2) := by
    have hs : ‖F t‖ ^ 2 ≤ (B / |t|) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (div_nonneg hB (abs_nonneg _))).2
        (hhigh t (abs_pos.mp ht))
    calc
      _ ≤ (1 + Real.log (1 + |t|)) * (B / |t|) ^ 2 :=
        mul_le_mul_of_nonneg_left hs (logarithmic_weight_nonneg t)
      _ = _ := by rw [div_pow]; ring
  have hpoint (t : ℝ) : H t ≤ G t := by
    by_cases ht : |t| ≤ R
    · have htC : t ∈ Icc (-R) R := abs_le.mp ht
      have hs : ‖F t‖ ^ 2 ≤ A ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hA).2 (hlow t)
      have hw : 1 + Real.log (1 + |t|) ≤ 1 + Real.log (1 + R) := by
        have hlog : Real.log (1 + |t|) ≤ Real.log (1 + R) :=
          Real.log_le_log (by linarith [abs_nonneg t]) (add_le_add le_rfl ht)
        exact add_le_add le_rfl hlog
      have hc : H t ≤ C t := by
        dsimp only [C]
        rw [indicator_of_mem htC]
        calc
          _ ≤ (1 + Real.log (1 + |t|)) * A ^ 2 :=
            mul_le_mul_of_nonneg_left hs (logarithmic_weight_nonneg t)
          _ ≤ (1 + Real.log (1 + R)) * A ^ 2 :=
            mul_le_mul_of_nonneg_right hw (sq_nonneg A)
          _ = _ := by ring
      dsimp [G]
      linarith [hP_nonneg t, hP_nonneg (-t)]
    · have htR : R < |t| := lt_of_not_ge ht
      have htpos : 0 < |t| := hR.trans htR
      by_cases ht0 : 0 ≤ t
      · have htP : t ∈ Ioi R := by
          change R < t
          simpa only [abs_of_nonneg ht0] using htR
        have hb : H t ≤ P t := by
          simpa only [P, indicator_of_mem htP, abs_of_nonneg ht0] using hdecay t htpos
        dsimp [G]
        linarith [hC_nonneg t, hP_nonneg (-t)]
      · have htneg : t < 0 := lt_of_not_ge ht0
        have htP : -t ∈ Ioi R := by
          change R < -t
          simpa only [abs_of_neg htneg] using htR
        have hb : H t ≤ P (-t) := by
          simpa only [P, indicator_of_mem htP, abs_of_neg htneg] using hdecay t htpos
        dsimp [G]
        linarith [hC_nonneg t, hP_nonneg t]
  have hH : Integrable H := hG.mono_nonneg
    (continuous_logarithmic_weight.mul (hF.norm.pow 2)).aestronglyMeasurable
    (Eventually.of_forall (fun t =>
      mul_nonneg (logarithmic_weight_nonneg t) (sq_nonneg ‖F t‖)))
    (Eventually.of_forall hpoint)
  have hC_integral : (∫ t : ℝ, C t) =
      2 * A ^ 2 * R * (1 + Real.log (1 + R)) := by
    dsimp [C]
    rw [integral_indicator measurableSet_Icc, setIntegral_const]
    simp only [Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R), smul_eq_mul]
    ring
  have hP_integral : (∫ t : ℝ, P t) =
      B ^ 2 * (∫ t : ℝ in Ioi R, (1 + Real.log (1 + t)) / t ^ 2) := by
    dsimp [P]
    rw [integral_indicator measurableSet_Ioi, integral_const_mul]
  refine ⟨hH, ?_⟩
  change (∫ t : ℝ, H t) ≤ _
  calc
    _ ≤ ∫ t : ℝ, G t := integral_mono hH hG hpoint
    _ = 2 * A ^ 2 * R * (1 + Real.log (1 + R)) +
        2 * B ^ 2 * (∫ t : ℝ in Ioi R, (1 + Real.log (1 + t)) / t ^ 2) := by
      dsimp only [G]
      rw [integral_add hCP hPn, integral_add hC hP,
        integral_neg_eq_self P volume, hC_integral, hP_integral]
      ring
    _ ≤ _ := by
      have ht := mul_le_mul_of_nonneg_left (integral_logarithmic_tail_le hR)
        (show 0 ≤ 2 * B ^ 2 by positivity)
      calc
        _ ≤ 2 * A ^ 2 * R * (1 + Real.log (1 + R)) +
            (2 * B ^ 2) * ((2 + Real.log (1 + R)) / R) := add_le_add le_rfl ht
        _ = _ := by ring

/-- The actual error has logarithmically weighted Fourier integrability,
and its angular norm squared obeys the explicit h-logarithm rate. -/
theorem sameWindowSmoothTrial_logarithmic_error_le (a h M M1 : ℝ)
    (hh : 0 < h) (ha : 4 * h ≤ a) (hM : 0 ≤ M) (hM1 : 0 ≤ M1)
    (p : ℝ → ℂ) (hp : ContDiff ℝ ∞ p) (heven : ∀ x, p (-x) = p x)
    (hbound : ∀ x ∈ Icc (-a) a, ‖p x‖ ≤ M)
    (hbound1 : ∀ x ∈ Icc (-a) a, ‖deriv p x‖ ≤ M1) :
    Integrable (fun t : ℝ => (1 + Real.log (1 + |t|)) *
      ‖sameWindowErrorFourier a h hh p hp heven t‖ ^ 2) ∧
      0 ≤ sameWindowLogarithmicError a p hp heven h ∧
      sameWindowLogarithmicError a p hp heven h ≤
        (h / Real.pi) * (16 * M ^ 2 + (4 * M + a * M1) ^ 2) *
          (2 + Real.log (1 + 1 / h)) := by
  have hpack := sameWindowSmoothTrial_fourier_error_bounds a h M M1 hh ha hM hM1
    p hp heven hbound hbound1
  let E : ℝ → ℂ := fun x => (Ioo (-a) a).indicator p x -
    sameWindowSmoothTrial a h hh p hp heven x
  let F : ℝ → ℂ := sameWindowErrorFourier a h hh p hp heven
  have hF : Continuous F := by
    change Continuous (fun t : ℝ => ∫ x : ℝ, fourierKernel (t : ℂ) x * E x)
    apply continuous_of_dominated (bound := fun x => ‖E x‖)
    · intro t
      exact (hpack.2 t).1.aestronglyMeasurable
    · intro t
      exact Eventually.of_forall (fun x => by
        rw [norm_mul, angular_kernel_norm, one_mul])
    · exact hpack.1.norm
    · apply Eventually.of_forall
      intro x
      change Continuous (fun t : ℝ => Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) * E x)
      fun_prop
  have henv := logarithmic_envelope F hF (4 * M * h) (4 * M + 4 * h * M1) (1 / h)
    (by positivity) (by positivity) (one_div_pos.mpr hh)
    (fun t => (hpack.2 t).2.1) (fun t ht => (hpack.2 t).2.2 ht)
  have hfactor : 0 ≤ inverseFourierFactor := by
    unfold inverseFourierFactor
    positivity
  have hlog : 0 ≤ Real.log (1 + 1 / h) :=
    Real.log_nonneg (by linarith [one_div_pos.mpr hh])
  have hB : 0 ≤ 4 * M + 4 * h * M1 := by positivity
  have hB' : 0 ≤ 4 * M + a * M1 := by
    have hapos : 0 < a := by linarith
    positivity
  have hBsq : (4 * M + 4 * h * M1) ^ 2 ≤ (4 * M + a * M1) ^ 2 := by
    apply (sq_le_sq₀ hB hB').2
    have hm := mul_le_mul_of_nonneg_right ha hM1
    nlinarith
  refine ⟨henv.1, ?_, ?_⟩
  · rw [sameWindowLogarithmicError, dif_pos hh]
    apply mul_nonneg hfactor
    apply integral_nonneg
    intro t
    exact mul_nonneg (logarithmic_weight_nonneg t) (sq_nonneg _)
  · rw [sameWindowLogarithmicError, dif_pos hh]
    calc
      _ ≤ inverseFourierFactor *
          (2 * (4 * M * h) ^ 2 * (1 / h) * (1 + Real.log (1 + 1 / h)) +
            2 * (4 * M + 4 * h * M1) ^ 2 * (2 + Real.log (1 + 1 / h)) / (1 / h)) :=
        mul_le_mul_of_nonneg_left henv.2 hfactor
      _ = (h / Real.pi) *
          (16 * M ^ 2 * (1 + Real.log (1 + 1 / h)) +
            (4 * M + 4 * h * M1) ^ 2 * (2 + Real.log (1 + 1 / h))) := by
        unfold inverseFourierFactor
        field_simp [hh.ne', Real.pi_ne_zero]; ring
      _ ≤ (h / Real.pi) *
          ((16 * M ^ 2 + (4 * M + a * M1) ^ 2) *
            (2 + Real.log (1 + 1 / h))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hfirst := mul_le_mul_of_nonneg_left
          (show 1 + Real.log (1 + 1 / h) ≤ 2 + Real.log (1 + 1 / h) by linarith)
          (show 0 ≤ 16 * M ^ 2 by positivity)
        have hsecond := mul_le_mul_of_nonneg_right hBsq
          (show 0 ≤ 2 + Real.log (1 + 1 / h) by linarith)
        calc
          _ ≤ 16 * M ^ 2 * (2 + Real.log (1 + 1 / h)) +
              (4 * M + a * M1) ^ 2 * (2 + Real.log (1 + 1 / h)) :=
            add_le_add hfirst hsecond
          _ = _ := by ring
      _ = _ := by ring

private theorem tendsto_logarithmic_width_rate :
    Tendsto (fun h : ℝ => h * (2 + Real.log (1 + 1 / h))) (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hlog1 : Tendsto (fun h : ℝ => Real.log (1 + h)) (𝓝[>] 0) (𝓝 0) := by
    have hs : Tendsto (fun h : ℝ => 1 + h) (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
      simpa only [add_zero] using (tendsto_const_nhds.add hid)
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hs
  have hlog0 : Tendsto (fun h : ℝ => h * Real.log h) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using
      (tendsto_log_mul_rpow_nhdsGT_zero (r := 1) (by norm_num))
  have hcombo : Tendsto
      (fun h : ℝ => 2 * h + h * Real.log (1 + h) - h * Real.log h)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, add_zero, sub_zero] using
      ((hid.const_mul 2).add (hid.mul hlog1)).sub hlog0
  apply hcombo.congr'
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  filter_upwards [hpos] with h hh
  have heq : Real.log (1 + 1 / h) = Real.log (1 + h) - Real.log h := by
    rw [show 1 + 1 / h = (1 + h) / h by field_simp; ring,
      Real.log_div (by positivity : (1 + h) ≠ 0) hh.ne']
  rw [heq]
  ring

/-- For every fixed smooth even input, the actual logarithmic Fourier error
of the same-window test tends to zero as the positive width tends to zero. -/
theorem tendsto_sameWindowSmoothTrial_logarithmic_error (a M M1 : ℝ)
    (ha : 0 < a) (hM : 0 ≤ M) (hM1 : 0 ≤ M1)
    (p : ℝ → ℂ) (hp : ContDiff ℝ ∞ p) (heven : ∀ x, p (-x) = p x)
    (hbound : ∀ x ∈ Icc (-a) a, ‖p x‖ ≤ M)
    (hbound1 : ∀ x ∈ Icc (-a) a, ‖deriv p x‖ ≤ M1) :
    Tendsto (sameWindowLogarithmicError a p hp heven) (𝓝[>] 0) (𝓝 0) := by
  let C : ℝ := (16 * M ^ 2 + (4 * M + a * M1) ^ 2) / Real.pi
  have hupper : Tendsto
      (fun h : ℝ => C * (h * (2 + Real.log (1 + 1 / h)))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using tendsto_logarithmic_width_rate.const_mul C
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < a / 4 :=
    hid.eventually (Iio_mem_nhds (by positivity : 0 < a / 4))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [hpos, hsmall] with h hh hs
    exact (sameWindowSmoothTrial_logarithmic_error_le a h M M1 hh (by linarith)
      hM hM1 p hp heven hbound hbound1).2.1
  · filter_upwards [hpos, hsmall] with h hh hs
    have hb := (sameWindowSmoothTrial_logarithmic_error_le a h M M1 hh (by linarith)
      hM hM1 p hp heven hbound hbound1).2.2
    calc
      _ ≤ (h / Real.pi) * (16 * M ^ 2 + (4 * M + a * M1) ^ 2) *
          (2 + Real.log (1 + 1 / h)) := hb
      _ = _ := by dsimp [C]; ring

#print axioms sameWindowSmoothTrial_logarithmic_error_le
#print axioms tendsto_sameWindowSmoothTrial_logarithmic_error

end D5.S3.Weil.BurnolGram.SameWindowLogarithmicError
