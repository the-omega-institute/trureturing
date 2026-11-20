/- GID: D5/S3/Analytic/Asymptotics/CommonPhaseSpectralCurvature
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/CommonPhaseSpectralCurvature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A divergent real second moment forces spectral curvature to diverge at a common phase. -/

import D5.S3.Analytic.Asymptotics.CosineSecondMoment
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Spectral curvature at a common phase

The real and imaginary weights already include the damping at the common
phase. The symmetric second difference is four times the real cosine
defect with a quadratic error controlled by the real weights and the
absolute first moment of the imaginary weights.
-/

open Filter
open scoped BigOperators Topology

set_option autoImplicit false

namespace CommonPhaseSpectralCurvature

noncomputable def spectralTerm (A B damping freq : ℕ → ℝ) (h : ℝ) (j : ℕ) : ℝ :=
  Real.exp (damping j * h) *
    (A j * Real.cos (freq j * h) - B j * Real.sin (freq j * h))

noncomputable def spectralSeries (A B damping freq : ℕ → ℝ) (h : ℝ) : ℝ :=
  -2 * (∑' j, spectralTerm A B damping freq h j)

theorem summable_abs_spectralTerm (A B damping freq : ℕ → ℝ)
    (hA_nonneg : ∀ j, 0 ≤ A j) (hA : Summable A) (hB : Summable (fun j => |B j|))
    (hdamping : ∀ j, |damping j| ≤ 1) (h : ℝ) :
    Summable (fun j => |spectralTerm A B damping freq h j|) := by
  refine Summable.of_nonneg_of_le (fun j => abs_nonneg _) ?_
    ((hA.add hB).mul_left (Real.exp |h|))
  intro j
  have hdamping_h : |damping j * h| ≤ |h| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg h) (hdamping j)
  have hexp : Real.exp (damping j * h) ≤ Real.exp |h| :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans hdamping_h)
  have hcos : |A j * Real.cos (freq j * h)| ≤ A j := by
    rw [abs_mul, abs_of_nonneg (hA_nonneg j)]
    exact mul_le_of_le_one_right (hA_nonneg j) (Real.abs_cos_le_one _)
  have hsin : |B j * Real.sin (freq j * h)| ≤ |B j| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  rw [spectralTerm, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (damping j * h) * (A j + |B j|) :=
      mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hcos hsin)) (Real.exp_pos _).le
    _ ≤ Real.exp |h| * (A j + |B j|) :=
      mul_le_mul_of_nonneg_right hexp (add_nonneg (hA_nonneg j) (abs_nonneg _))

private theorem abs_cosh_sub_one_le_sq {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cosh x - 1| ≤ x ^ 2 := by
  have hneg : |-x| ≤ 1 := by simpa only [abs_neg] using hx
  have hpos_bound := Real.abs_exp_sub_one_sub_id_le hx
  have hneg_bound := Real.abs_exp_sub_one_sub_id_le hneg
  rw [neg_sq] at hneg_bound
  have hsplit : Real.cosh x - 1 =
      ((Real.exp x - 1 - x) + (Real.exp (-x) - 1 - (-x))) / 2 := by
    rw [Real.cosh_eq]
    ring
  rw [hsplit, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  calc
    _ ≤ |Real.exp x - 1 - x| + |Real.exp (-x) - 1 - (-x)| := abs_add_le _ _
    _ ≤ x ^ 2 + x ^ 2 := add_le_add hpos_bound hneg_bound
    _ = _ := by ring

private theorem abs_sinh_le_two_mul_abs {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sinh x| ≤ 2 * |x| := by
  have hneg : |-x| ≤ 1 := by simpa only [abs_neg] using hx
  have hpos_bound := Real.abs_exp_sub_one_le hx
  have hneg_bound := Real.abs_exp_sub_one_le hneg
  rw [abs_neg] at hneg_bound
  have hsplit : Real.sinh x = ((Real.exp x - 1) - (Real.exp (-x) - 1)) / 2 := by
    rw [Real.sinh_eq]
    ring
  rw [hsplit, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  calc
    _ ≤ |Real.exp x - 1| + |Real.exp (-x) - 1| := abs_sub _ _
    _ ≤ 2 * |x| + 2 * |x| := add_le_add hpos_bound hneg_bound
    _ = _ := by ring

private noncomputable def spectralRemainder (A B damping freq : ℕ → ℝ) (h : ℝ) (j : ℕ) : ℝ :=
  B j * Real.sinh (damping j * h) * Real.sin (freq j * h) -
    A j * (Real.cosh (damping j * h) - 1) * Real.cos (freq j * h)

private theorem abs_spectralRemainder_le (A B damping freq : ℕ → ℝ)
    (hA_nonneg : ∀ j, 0 ≤ A j) (hdamping : ∀ j, |damping j| ≤ 1)
    {h : ℝ} (hh : |h| ≤ 1) (j : ℕ) :
    |spectralRemainder A B damping freq h j| ≤ h ^ 2 * (A j + 2 * |B j * freq j|) := by
  have hdamping_h : |damping j * h| ≤ |h| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg h) (hdamping j)
  have hcosh : |Real.cosh (damping j * h) - 1| ≤ h ^ 2 :=
    (abs_cosh_sub_one_le_sq (hdamping_h.trans hh)).trans (sq_le_sq.2 hdamping_h)
  have hsinh : |Real.sinh (damping j * h)| ≤ 2 * |h| :=
    (abs_sinh_le_two_mul_abs (hdamping_h.trans hh)).trans
      (mul_le_mul_of_nonneg_left hdamping_h (by norm_num))
  have hreal : |A j * (Real.cosh (damping j * h) - 1) * Real.cos (freq j * h)| ≤
      A j * h ^ 2 := by
    simp only [abs_mul, abs_of_nonneg (hA_nonneg j)]
    calc
      _ ≤ A j * |Real.cosh (damping j * h) - 1| :=
        mul_le_of_le_one_right (mul_nonneg (hA_nonneg j) (abs_nonneg _)) (Real.abs_cos_le_one _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hcosh (hA_nonneg j)
  have himag : |B j * Real.sinh (damping j * h) * Real.sin (freq j * h)| ≤
      2 * |B j * freq j| * h ^ 2 := by
    calc
      _ = |B j| * |Real.sinh (damping j * h)| * |Real.sin (freq j * h)| := by
        simp only [abs_mul]
      _ ≤ |B j| * (2 * |h|) * |freq j * h| :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsinh (abs_nonneg _)) Real.abs_sin_le_abs
          (abs_nonneg _) (mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _)))
      _ = _ := by
        simp only [abs_mul, ← sq_abs h]
        ring
  unfold spectralRemainder
  calc
    _ ≤ |B j * Real.sinh (damping j * h) * Real.sin (freq j * h)| +
        |A j * (Real.cosh (damping j * h) - 1) * Real.cos (freq j * h)| := abs_sub _ _
    _ ≤ 2 * |B j * freq j| * h ^ 2 + A j * h ^ 2 := add_le_add himag hreal
    _ = _ := by ring

/-- The symmetric second difference is four times the cosine defect up to a quadratic error. -/
theorem abs_symmetric_second_difference_sub_cosine_defect_le (A B damping freq : ℕ → ℝ)
    (hA_nonneg : ∀ j, 0 ≤ A j) (hA : Summable A) (hB : Summable (fun j => |B j|))
    (hBfreq : Summable (fun j => |B j * freq j|)) (hdamping : ∀ j, |damping j| ≤ 1)
    {h : ℝ} (hh : |h| ≤ 1) :
    |spectralSeries A B damping freq h + spectralSeries A B damping freq (-h) -
      2 * spectralSeries A B damping freq 0 - 4 * (∑' j, A j * (1 - Real.cos (freq j * h)))| ≤
      4 * h ^ 2 * (∑' j, (A j + 2 * |B j * freq j|)) := by
  let defect : ℕ → ℝ := fun j => A j * (1 - Real.cos (freq j * h))
  let err : ℕ → ℝ := spectralRemainder A B damping freq h
  have hdefect : Summable defect := by
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (hA.mul_left 2)
    · exact mul_nonneg (hA_nonneg j) (sub_nonneg.mpr (Real.cos_le_one _))
    · change A j * (1 - Real.cos (freq j * h)) ≤ 2 * A j
      calc
        _ ≤ A j * (1 - (-1 : ℝ)) :=
          mul_le_mul_of_nonneg_left (sub_le_sub_left (Real.neg_one_le_cos _) 1) (hA_nonneg j)
        _ = _ := by ring
  have hmajor : Summable (fun j => A j + 2 * |B j * freq j|) := hA.add (hBfreq.mul_left 2)
  have hscaled := hmajor.mul_left (h ^ 2)
  have hbound (j : ℕ) : ‖err j‖ ≤ h ^ 2 * (A j + 2 * |B j * freq j|) := by
    rw [Real.norm_eq_abs]
    exact abs_spectralRemainder_le A B damping freq hA_nonneg hdamping hh j
  have herr : Summable err := hscaled.of_norm_bounded hbound
  have habs : |∑' j, err j| ≤ h ^ 2 * (∑' j, (A j + 2 * |B j * freq j|)) := by
    simpa only [Real.norm_eq_abs, hmajor.tsum_mul_left (h ^ 2)] using
      (herr.hasSum.norm_le_of_bounded hscaled.hasSum hbound)
  have hpos := (summable_abs_spectralTerm A B damping freq hA_nonneg hA hB hdamping h).of_abs
  have hneg := (summable_abs_spectralTerm A B damping freq hA_nonneg hA hB hdamping (-h)).of_abs
  have hzero : spectralSeries A B damping freq 0 = -2 * (∑' j, A j) := by
    simp [spectralSeries, spectralTerm]
  have hterm (j : ℕ) :
      (-2 : ℝ) * (spectralTerm A B damping freq h j + spectralTerm A B damping freq (-h) j -
        2 * A j) = 4 * (defect j + err j) := by
    simp only [spectralTerm, defect, err, spectralRemainder, mul_neg, Real.cos_neg, Real.sin_neg,
      Real.cosh_eq, Real.sinh_eq]
    ring
  have hpair : spectralSeries A B damping freq h + spectralSeries A B damping freq (-h) -
      2 * spectralSeries A B damping freq 0 = 4 * ((∑' j, defect j) + (∑' j, err j)) := by
    calc
      _ = -2 * ((∑' j, spectralTerm A B damping freq h j) +
          (∑' j, spectralTerm A B damping freq (-h) j) - 2 * (∑' j, A j)) := by
        rw [hzero]
        unfold spectralSeries
        ring
      _ = -2 * (∑' j, (spectralTerm A B damping freq h j +
          spectralTerm A B damping freq (-h) j - 2 * A j)) := by
        rw [(hpos.add hneg).tsum_sub (hA.mul_left 2), hpos.tsum_add hneg, hA.tsum_mul_left 2]
      _ = ∑' j, (-2 : ℝ) * (spectralTerm A B damping freq h j +
          spectralTerm A B damping freq (-h) j - 2 * A j) :=
        (((hpos.add hneg).sub (hA.mul_left 2)).tsum_mul_left (-2)).symm
      _ = ∑' j, 4 * (defect j + err j) := tsum_congr hterm
      _ = _ := by rw [(hdefect.add herr).tsum_mul_left 4, hdefect.tsum_add herr]
  have hscaled_abs : |4 * (∑' j, err j)| ≤
      4 * h ^ 2 * (∑' j, (A j + 2 * |B j * freq j|)) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), mul_assoc]
    exact mul_le_mul_of_nonneg_left habs (by norm_num)
  have herror_eq : 4 * ((∑' j, defect j) + (∑' j, err j)) - 4 * (∑' j, defect j) =
      4 * (∑' j, err j) := by ring
  change |spectralSeries A B damping freq h + spectralSeries A B damping freq (-h) -
    2 * spectralSeries A B damping freq 0 - 4 * (∑' j, defect j)| ≤ _
  rw [hpair, herror_eq]
  exact hscaled_abs

/-- A divergent weighted second moment forces the normalized spectral second difference to
tend to positive infinity at the common phase. -/
theorem tendsto_symmetric_second_difference_div_sq_atTop (A B damping freq : ℕ → ℝ)
    (hA_nonneg : ∀ j, 0 ≤ A j) (hA : Summable A) (hB : Summable (fun j => |B j|))
    (hBfreq : Summable (fun j => |B j * freq j|)) (hdamping : ∀ j, |damping j| ≤ 1)
    (hmoment : ¬ Summable (fun j => A j * (freq j) ^ 2)) :
    Tendsto (fun h : ℝ => (spectralSeries A B damping freq h +
      spectralSeries A B damping freq (-h) - 2 * spectralSeries A B damping freq 0) / h ^ 2)
      (𝓝[≠] 0) atTop := by
  let C : ℝ := ∑' j, (A j + 2 * |B j * freq j|)
  let D : ℝ → ℝ := fun h => ∑' j, A j * (1 - Real.cos (freq j * h))
  have hmain : Tendsto (fun h => D h / h ^ 2) (𝓝[≠] 0) atTop :=
    CosineSecondMoment.tendsto_cosine_defect_div_sq_atTop A freq hA_nonneg hA hmoment
  have hsmall : ∀ᶠ h : ℝ in 𝓝[≠] (0 : ℝ), |h| ≤ 1 := by
    apply eventually_nhdsWithin_of_eventually_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (zero_lt_one : (0 : ℝ) < 1)] with h hh
    have hlt : |h| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hh
    exact hlt.le
  have hne : ∀ᶠ h : ℝ in 𝓝[≠] (0 : ℝ), h ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := ({0} : Set ℝ)ᶜ))
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [tendsto_atTop.1 hmain (M / 4 + C), hsmall, hne] with h hlarge hh hzero
  have hsq : 0 < h ^ 2 := sq_pos_of_ne_zero hzero
  have hlower : (M / 4 + C) * h ^ 2 ≤ D h := (le_div_iff₀ hsq).1 hlarge
  have habs := abs_symmetric_second_difference_sub_cosine_defect_le A B damping freq
    hA_nonneg hA hB hBfreq hdamping hh
  have herr : -(4 * h ^ 2 * C) ≤ spectralSeries A B damping freq h +
      spectralSeries A B damping freq (-h) - 2 * spectralSeries A B damping freq 0 - 4 * D h :=
    (abs_le.mp habs).1
  apply (le_div_iff₀ hsq).2
  calc
    M * h ^ 2 = 4 * ((M / 4 + C) * h ^ 2) - 4 * h ^ 2 * C := by ring
    _ ≤ 4 * D h - 4 * h ^ 2 * C :=
      sub_le_sub_right (mul_le_mul_of_nonneg_left hlower (by norm_num)) _
    _ ≤ _ := by
      simpa only [sub_eq_add_neg, add_comm] using (le_sub_iff_add_le).1 herr

end CommonPhaseSpectralCurvature
