/- GID: D5/S3/Fourier/HarmonicScoreLocalAverage
   generality: G
   mirror-B: D5/B/S3/Fourier/HarmonicScoreLocalAverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local averaging gives a three-band lower bound for a finite weighted sine score. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-! Local averaging of a finite weighted sine score on an arbitrary interval. -/

set_option autoImplicit false

open MeasureTheory Set
open scoped BigOperators

namespace D5.S3.Fourier.HarmonicScoreLocalAverage

noncomputable section

private def cutoff {J : Type*} (s : Finset J) (g : J → ℝ) (Z : ℝ) : Finset J := by
  classical
  exact s.filter (fun j => g j ≤ Z)

/-- Sum of the weights at frequencies at most the cutoff. -/
def cutoffMass {J : Type*} (s : Finset J) (g w : J → ℝ) (Z : ℝ) : ℝ :=
  ∑ j ∈ cutoff s g Z, w j

/-- Weighted sine score at frequencies at most the cutoff. -/
def cutoffScore {J : Type*} (s : Finset J) (g w : J → ℝ) (Z v : ℝ) : ℝ :=
  ∑ j ∈ cutoff s g Z, w j * Real.sin (g j * v)

private theorem le_sine_mean_of_le_on {g r b h c : ℝ} (hh : 0 < h)
    (hc : ∀ u ∈ Icc b (b + h), c ≤ Real.sin (g * (u / r))) :
    c ≤ (1 / h) * (∫ u in b..b + h, Real.sin (g * (u / r))) := by
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    (show b ≤ b + h by linarith)
    ((continuous_const (y := c)).intervalIntegrable b (b + h))
    ((show Continuous (fun u : ℝ => Real.sin (g * (u / r))) by
      fun_prop).intervalIntegrable b (b + h)) hc
  rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hmono
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hh]
  simpa only [mul_comm c h] using hmono

private theorem tail_sine_mean_lower {g Y r b h : ℝ} (hY : 0 < Y) (hg : Y < g)
    (hr : 0 < r) (hh : 0 < h) :
    -(2 * r / (h * Y)) ≤ (1 / h) * (∫ u in b..b + h, Real.sin (g * (u / r))) := by
  have hgpos : 0 < g := hY.trans hg
  simp_rw [show ∀ u : ℝ, g * (u / r) = (g / r) * u by intro u; ring]
  rw [intervalIntegral.integral_comp_mul_left Real.sin (div_pos hgpos hr).ne', integral_sin,
    smul_eq_mul, ← mul_assoc]
  have hcoeff : 0 ≤ (1 / h) * (g / r)⁻¹ := by positivity
  have hcos : -2 ≤ Real.cos (g / r * b) - Real.cos (g / r * (b + h)) := by
    linarith [Real.neg_one_le_cos (g / r * b), Real.cos_le_one (g / r * (b + h))]
  calc
    _ ≤ -(2 * r / (h * g)) := by
      have hden : h * Y ≤ h * g := mul_le_mul_of_nonneg_left hg.le hh.le
      exact neg_le_neg (div_le_div_of_nonneg_left (by positivity) (mul_pos hh hY) hden)
    _ = (1 / h) * (g / r)⁻¹ * (-2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hcos hcoeff

/-- The average full score over the window has a lower bound from the score at its left
endpoint, with separate losses for the head, middle and tail bands. -/
theorem cutoffScore_average_lower {J : Type*} (s : Finset J) (g w : J → ℝ)
    {X Y T r h b : ℝ} (hX : 0 < X) (hXY : X ≤ Y) (hYT : Y ≤ T)
    (hr : 0 < r) (hh : 0 < h) (hg : ∀ j ∈ s, 0 < g j) (hw : ∀ j ∈ s, 0 ≤ w j) :
    cutoffScore s g w X (b / r) - (h * X / r) * cutoffMass s g w X -
        (cutoffMass s g w Y - cutoffMass s g w X) -
        (2 * r / (h * Y)) * (cutoffMass s g w T - cutoffMass s g w Y) ≤
      (1 / h) * (∫ u in b..b + h, cutoffScore s g w T (u / r)) := by
  classical
  let head := cutoff s g X
  let upper := cutoff s g Y
  let full := cutoff s g T
  let middle := upper \ head
  let tail := full \ upper
  let mean (j : J) := (1 / h) * (∫ u in b..b + h, Real.sin (g j * (u / r)))
  have hcut (Z : ℝ) (j : J) : j ∈ cutoff s g Z ↔ j ∈ s ∧ g j ≤ Z := Finset.mem_filter
  have hhead : head ⊆ upper := fun j hj =>
    (hcut Y j).mpr ⟨((hcut X j).mp hj).1, ((hcut X j).mp hj).2.trans hXY⟩
  have hupper : upper ⊆ full := fun j hj =>
    (hcut T j).mpr ⟨((hcut Y j).mp hj).1, ((hcut Y j).mp hj).2.trans hYT⟩
  have hheadMean : (∑ j ∈ head, w j * Real.sin (g j * (b / r))) -
        (h * X / r) * (∑ j ∈ head, w j) ≤ ∑ j ∈ head, w j * mean j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have ⟨hjs, hjX⟩ := (hcut X j).mp hj
    rw [mul_comm (h * X / r), ← mul_sub]
    apply mul_le_mul_of_nonneg_left (le_sine_mean_of_le_on hh ?_) (hw j hjs)
    intro u hu
    have hshift : 0 ≤ u - b := sub_nonneg.mpr hu.1
    have hangle : g j * (u / r) - g j * (b / r) = g j * (u - b) / r := by ring
    have hjpos := hg j hjs
    have hangle_nonneg : 0 ≤ g j * (u - b) / r := by positivity
    have habs := Real.abs_sin_sub_sin_le (g j * (b / r)) (g j * (u / r))
    rw [abs_sub_comm (g j * (b / r)), hangle, abs_of_nonneg hangle_nonneg] at habs
    have hcost : g j * (u - b) / r ≤ h * X / r := by
      apply div_le_div_of_nonneg_right _ hr.le
      exact (mul_le_mul_of_nonneg_right hjX hshift).trans
        (by
          have hlen : u - b ≤ h := by linarith [hu.2]
          simpa only [mul_comm X h] using mul_le_mul_of_nonneg_left hlen hX.le)
    linarith [(le_abs_self _).trans (habs.trans hcost)]
  have hmiddleMean : -(∑ j ∈ middle, w j) ≤ ∑ j ∈ middle, w j * mean j := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have hjs := ((hcut Y j).mp (Finset.mem_sdiff.mp hj).1).1
    simpa only [mul_neg, mul_one] using
      mul_le_mul_of_nonneg_left (le_sine_mean_of_le_on (g := g j) (r := r) hh
        (fun u _ => Real.neg_one_le_sin (g j * (u / r)))) (hw j hjs)
  have htailMean : -(2 * r / (h * Y)) * (∑ j ∈ tail, w j) ≤
      ∑ j ∈ tail, w j * mean j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have ⟨hjT, hjY⟩ := Finset.mem_sdiff.mp hj
    have hjs := ((hcut T j).mp hjT).1
    have hYj : Y < g j := lt_of_not_ge (fun h => hjY ((hcut Y j).mpr ⟨hjs, h⟩))
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (tail_sine_mean_lower (hX.trans_le hXY) hYj hr hh)
      (hw j hjs)
  have mass_middle : (∑ j ∈ middle, w j) =
      cutoffMass s g w Y - cutoffMass s g w X := by
    exact eq_sub_of_add_eq (Finset.sum_sdiff hhead)
  have mass_tail : (∑ j ∈ tail, w j) =
      cutoffMass s g w T - cutoffMass s g w Y := by
    exact eq_sub_of_add_eq (Finset.sum_sdiff hupper)
  have hmean : (1 / h) * (∫ u in b..b + h, cutoffScore s g w T (u / r)) =
      ∑ j ∈ full, w j * mean j := by
    unfold cutoffScore
    rw [intervalIntegral.integral_finsetSum (fun j _ => by
      apply Continuous.intervalIntegrable
      fun_prop), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul]
    dsimp [mean]
    ring
  rw [hmean, ← Finset.sum_sdiff hupper, ← Finset.sum_sdiff hhead,
    ← mass_middle, ← mass_tail]
  change (∑ j ∈ head, w j * Real.sin (g j * (b / r))) -
      (h * X / r) * (∑ j ∈ head, w j) - (∑ j ∈ middle, w j) -
      (2 * r / (h * Y)) * (∑ j ∈ tail, w j) ≤ _
  linarith

/-- The same lower bound holds at some point of the closed averaging window. -/
theorem exists_cutoffScore_ge {J : Type*} (s : Finset J) (g w : J → ℝ)
    {X Y T r h b : ℝ} (hX : 0 < X) (hXY : X ≤ Y) (hYT : Y ≤ T)
    (hr : 0 < r) (hh : 0 < h) (hg : ∀ j ∈ s, 0 < g j) (hw : ∀ j ∈ s, 0 ≤ w j) :
    ∃ u ∈ Icc b (b + h),
      cutoffScore s g w X (b / r) - (h * X / r) * cutoffMass s g w X -
          (cutoffMass s g w Y - cutoffMass s g w X) -
          (2 * r / (h * Y)) * (cutoffMass s g w T - cutoffMass s g w Y) ≤
        cutoffScore s g w T (u / r) := by
  let f (u : ℝ) := cutoffScore s g w T (u / r)
  have hf : Continuous f := by
    unfold f cutoffScore
    fun_prop
  obtain ⟨u, hu, heq⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (μ := volume) (a := b) (b := b + h) hf.continuousOn
    ((continuous_const (y := (1 : ℝ))).intervalIntegrable b (b + h)) (fun _ _ => zero_le_one)
  have hab : b ≤ b + h := by linarith
  rw [uIcc_of_le hab] at hu
  simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul,
    add_sub_cancel_left] at heq
  have havg : (1 / h) * (∫ v in b..b + h, f v) = f u := by
    rw [heq]
    field_simp
  exact ⟨u, hu, (cutoffScore_average_lower s g w hX hXY hYT hr hh hg hw).trans_eq havg⟩

end

end D5.S3.Fourier.HarmonicScoreLocalAverage
