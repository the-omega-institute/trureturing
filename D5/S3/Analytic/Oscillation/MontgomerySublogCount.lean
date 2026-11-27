/- GID: D5/S3/Analytic/Oscillation/MontgomerySublogCount
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/MontgomerySublogCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sublogarithmic count discrepancy controls the uniform Montgomery leading coefficient. -/

import D5.S3.Analytic.Oscillation.MontgomeryCountUpper

/-! The inclusive counting error controls the Lorentz pair sum at each cutoff. -/

open Filter
open scoped Topology

noncomputable section

namespace D5.S3.Analytic.Oscillation.MontgomerySublogCount

open OrdinateCounting (Spectrum CountAsymptotic)
open MontgomeryCountUpper (pairSum abs_pairSum_le_of_local_discrepancy)
open SmoothedSpectrumCounting.CutDensity (countMain)

private abbrev c : ℝ := 1 / (2 * Real.pi)
private abbrev C : ℝ := 2 * Real.pi

private theorem uniform_discrepancy (S : Spectrum) (C : ℝ)
    (err : Tendsto (fun x : ℝ => ((S.N x : ℝ) - countMain C x) / Real.log x) atTop (𝓝 0))
    {η : ℝ} (positive : 0 < η) :
    ∃ A : ℝ, 1 < A ∧ ∀ Y x, A ≤ x → x ≤ Y →
      |(S.N x : ℝ) - countMain C x| ≤ η * Real.log Y := by
  have absErr := err.abs
  rw [abs_zero] at absErr
  obtain ⟨a, ha⟩ := eventually_atTop.mp (absErr.eventually (gt_mem_nhds positive))
  refine ⟨max 2 a, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro Y x hx hxy
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) ((le_max_left 2 a).trans hx)
  have hl := Real.log_pos hx1
  have he := ha _ ((le_max_right 2 a).trans hx)
  rw [abs_div, abs_of_pos hl] at he
  exact ((div_lt_iff₀ hl).mp he).le.trans
    (mul_le_mul_of_nonneg_left (Real.log_le_log (zero_lt_one.trans hx1) hxy) positive.le)

/-- The leading counting asymptotic follows from the sublogarithmic discrepancy. -/
theorem countAsymptotic_of_sublog (S : Spectrum)
    (err : Tendsto (fun Y : ℝ => ((S.N Y : ℝ) - countMain C Y) / Real.log Y) atTop (𝓝 0)) :
    CountAsymptotic S := by
  have hC : 0 < C := by positivity
  have hshift : Tendsto (fun Y : ℝ => (Real.log C + 1) / Real.log Y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hmain : Tendsto (fun Y : ℝ => countMain C Y / (Y * Real.log Y)) atTop (𝓝 c) := by
    have h := (hshift.const_sub 1).const_mul c
    rw [sub_zero, mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
    rw [countMain, Real.log_div (zero_lt_one.trans hY).ne' hC.ne']
    dsimp [c, C] at *
    field_simp [(Real.log_pos hY).ne', (zero_lt_one.trans hY).ne', Real.pi_ne_zero]
    ring
  have he := err.mul (tendsto_inv_atTop_zero (𝕜 := ℝ))
  rw [zero_mul] at he
  have h := hmain.add he
  rw [add_zero] at h
  apply h.congr
  intro Y
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Sublogarithmic count discrepancy gives the sharp leading upper coefficient uniformly in phase. -/
theorem pairSum_le_of_sublog_discrepancy (S : Spectrum)
    (err : Tendsto (fun Y : ℝ => ((S.N Y : ℝ) - countMain C Y) / Real.log Y) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ Y : ℝ in atTop, ∀ t : ℝ,
      |pairSum S Y t| ≤ (2 * Real.pi * c ^ 2 + ε) * (Y * Real.log Y ^ 2) := by
  have hc : 0 < c := by positivity
  let η := ε / (4 * c)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨A, hA, hdisc⟩ := uniform_discrepancy S C err hη
  have hratio := countAsymptotic_of_sublog S err
  let B := (S.N A : ℝ) + c
  have hz : Tendsto (fun Y : ℝ => B / Real.log Y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hrow : Tendsto (fun Y : ℝ => 2 * Real.pi * c + 2 * η + B / Real.log Y)
      atTop (𝓝 (2 * Real.pi * c + 2 * η)) := by
    simpa using hz.const_add (2 * Real.pi * c + 2 * η)
  have hprod := hratio.mul hrow
  have hlt : c * (2 * Real.pi * c + 2 * η) < 2 * Real.pi * c ^ 2 + ε := by
    have hηeq : c * (2 * η) = ε / 2 := by dsimp [η]; field_simp; ring
    calc
      _ = 2 * Real.pi * c ^ 2 + c * (2 * η) := by ring
      _ < _ := by rw [hηeq]; linarith
  filter_upwards [hprod.eventually (gt_mem_nhds hlt), eventually_ge_atTop A] with Y hlim hY
  intro t
  have hlog := Real.log_pos (hA.trans_le hY)
  have hY0 := zero_lt_one.trans (hA.trans_le hY)
  apply (abs_pairSum_le_of_local_discrepancy S hA.le (hdisc Y) hY (hA.trans_le hY) t).trans
  calc
    _ = ((S.N Y : ℝ) / (Y * Real.log Y) *
        (2 * Real.pi * c + 2 * η + B / Real.log Y)) * (Y * Real.log Y ^ 2) := by
      dsimp [B]
      field_simp [hlog.ne', hY0.ne']
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hlim.le (by positivity)

end D5.S3.Analytic.Oscillation.MontgomerySublogCount
