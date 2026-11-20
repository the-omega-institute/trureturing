/- GID: D5/S3/Analytic/Asymptotics/PositiveAverageCosineWindow
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/PositiveAverageCosineWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A dominant cosine in compact probability averages forces both raw signs. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Compact probability averages of a signal near opposite cosine extrema. -/

open MeasureTheory Set

namespace PositiveAverageCosineWindow

private lemma exists_in_period {frequency : ℝ} (hfrequency : 0 < frequency)
    (start phase angle : ℝ) :
    ∃ t ∈ Ico start (start + 2 * Real.pi / frequency), ∃ k : ℤ,
      frequency * t + phase = angle + (k : ℝ) * (2 * Real.pi) := by
  let period : ℝ := 2 * Real.pi
  let z := (frequency * start + phase - angle) / period
  let k : ℤ := ⌈z⌉
  let t := (angle + (k : ℝ) * period - phase) / frequency
  have hperiod : 0 < period := mul_pos (by norm_num) Real.pi_pos
  have hz : z * period = frequency * start + phase - angle :=
    div_mul_cancel₀ _ hperiod.ne'
  have hlo := mul_le_mul_of_nonneg_right (Int.le_ceil z) hperiod.le
  have hhi := mul_lt_mul_of_pos_right (Int.ceil_lt_add_one z) hperiod
  rw [hz] at hlo
  rw [add_mul, hz, one_mul] at hhi
  refine ⟨t, ⟨?_, ?_⟩, k, ?_⟩
  · change start ≤ (angle + (k : ℝ) * period - phase) / frequency
    apply (le_div_iff₀ hfrequency).2
    linarith only [hlo]
  · change (angle + (k : ℝ) * period - phase) / frequency < start + period / frequency
    apply (div_lt_iff₀ hfrequency).2
    rw [add_mul, div_mul_cancel₀ _ hfrequency.ne']
    linarith only [hhi]
  · change frequency * ((angle + (k : ℝ) * period - phase) / frequency) + phase = _
    rw [mul_comm frequency, div_mul_cancel₀ _ hfrequency.ne', sub_add_cancel]

private lemma exists_of_lt_average {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {h level : ℝ} {f : ℝ → ℝ} (hν : ν (Icc 0 h) = 1) (hf : Integrable f ν)
    (havg : level < ∫ s, f s ∂ν) : ∃ s ∈ Icc 0 h, level < f s := by
  by_contra! hpoint
  have hs : ∀ᵐ s ∂ν, s ∈ Icc 0 h :=
    (mem_ae_iff_prob_eq_one measurableSet_Icc).2 hν
  have hle := integral_mono_ae hf (integrable_const level) (hs.mono hpoint)
  have : (∫ s, f s ∂ν) ≤ level := by
    simpa only [integral_const, probReal_univ, one_smul] using hle
  exact havg.not_ge this

/-- If a cosine dominates probability averages with short forward support, both signs
occur in the raw signal in a window enlarged by that support. The averaging measure
may depend on the starting point of each average. -/
theorem exists_signed_values {f scale : ℝ → ℝ}
    {start width support frequency phase amplitude lower : ℝ}
    (hfrequency : 0 < frequency) (hwidth : 2 * Real.pi / frequency ≤ width)
    (hamplitude : 0 < amplitude) (hlower : 0 < lower)
    (hscale : ∀ t ∈ Icc start (start + width), lower ≤ scale t)
    (happrox : ∀ t ∈ Icc start (start + width), ∃ ν : Measure ℝ,
      IsProbabilityMeasure ν ∧ ν (Icc 0 support) = 1 ∧
      Integrable (fun s => f (t + s)) ν ∧
      |(∫ s, f (t + s) ∂ν) -
        amplitude * scale t * Real.cos (frequency * t + phase)| ≤ amplitude * scale t / 2) :
    (∃ t ∈ Icc start (start + width + support), amplitude * lower / 4 < f t) ∧
    (∃ t ∈ Icc start (start + width + support), f t < -(amplitude * lower / 4)) := by
  obtain ⟨tPlus, htPlus, kPlus, hp⟩ := exists_in_period hfrequency start phase 0
  obtain ⟨tMinus, htMinus, kMinus, hm⟩ := exists_in_period hfrequency start phase Real.pi
  have htp : tPlus ∈ Icc start (start + width) :=
    ⟨htPlus.1, htPlus.2.le.trans (add_le_add_right hwidth _)⟩
  have htm : tMinus ∈ Icc start (start + width) :=
    ⟨htMinus.1, htMinus.2.le.trans (add_le_add_right hwidth _)⟩
  have hp' : Real.cos (frequency * tPlus + phase) = 1 := by
    rw [hp, zero_add, Real.cos_int_mul_two_pi]
  have hm' : Real.cos (frequency * tMinus + phase) = -1 := by
    rw [hm, add_comm Real.pi, Real.cos_int_mul_two_pi_add_pi]
  have hpositive := mul_pos hamplitude hlower
  constructor
  · obtain ⟨ν, hprob, hν, hf, happrox⟩ := happrox tPlus htp
    let _ : IsProbabilityMeasure ν := hprob
    have hbound := (abs_le.mp happrox).1
    rw [hp', mul_one] at hbound
    have hcompare := mul_le_mul_of_nonneg_left (hscale tPlus htp) hamplitude.le
    have hvalue : amplitude * lower / 4 < ∫ s, f (tPlus + s) ∂ν := by
      linarith only [hbound, hcompare, hpositive]
    obtain ⟨s, hs, hf⟩ := exists_of_lt_average hν hf hvalue
    exact ⟨tPlus + s, ⟨by linarith [htp.1, hs.1], add_le_add htp.2 hs.2⟩, hf⟩
  · obtain ⟨ν, hprob, hν, hf, happrox⟩ := happrox tMinus htm
    let _ : IsProbabilityMeasure ν := hprob
    have hbound := (abs_le.mp happrox).2
    rw [hm', mul_neg, mul_one] at hbound
    have hcompare := mul_le_mul_of_nonneg_left (hscale tMinus htm) hamplitude.le
    have hvalue : amplitude * lower / 4 < ∫ s, -f (tMinus + s) ∂ν := by
      rw [integral_neg]
      linarith only [hbound, hcompare, hpositive]
    obtain ⟨s, hs, hf⟩ := exists_of_lt_average hν hf.neg hvalue
    change amplitude * lower / 4 < -f (tMinus + s) at hf
    exact ⟨tMinus + s, ⟨by linarith [htm.1, hs.1], add_le_add htm.2 hs.2⟩,
      by linarith only [hf]⟩

end PositiveAverageCosineWindow
