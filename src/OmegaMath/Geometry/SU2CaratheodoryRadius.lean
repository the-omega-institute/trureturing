import OmegaMath.Geometry.SU2CaratheodoryCap
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import OmegaMath.Geometry.SU2ChordalIntervals

compile_only_with_mathlib

/-! Omega original.

Convexity and secant estimates for the four-contact spherical radius.
-/

open Real Set
noncomputable section

namespace Omega.Geometry.SU2Caratheodory

theorem sin_sq_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ π / 2) :
    sin x ^ 2 ≤ sin y ^ 2 := by
  have hs := strictMonoOn_sin.monotoneOn
    (show x ∈ Icc (-(π / 2)) (π / 2) from ⟨by linarith [pi_pos], hxy.trans hy⟩)
    (show y ∈ Icc (-(π / 2)) (π / 2) from ⟨by linarith [pi_pos], hy⟩) hxy
  exact pow_le_pow_left₀ (sin_nonneg_of_nonneg_of_le_pi hx (by linarith [pi_pos])) hs 2

private theorem radius_deriv {x : ℝ} (hx : 0 ≤ x) (hxπ : x ≤ π / 2)
    (ht : sin x ^ 2 ≤ 5 / 12) :
    HasDerivAt radius (√(3 / 2 : ℝ) * cos x / √(1 - (3 / 2) * sin x ^ 2)) x := by
  have ha : (√(3 / 2 : ℝ)) ^ 2 = 3 / 2 := sq_sqrt (by norm_num)
  have hs : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi hx (by linarith [pi_pos])
  have hb : 0 ≤ √(3 / 2 : ℝ) * sin x := by positivity
  have hb' : √(3 / 2 : ℝ) * sin x < 1 := by
    nlinarith [mul_pow (√(3 / 2 : ℝ)) (sin x) 2]
  have h := (hasDerivAt_arcsin (by linarith : √(3 / 2 : ℝ) * sin x ≠ -1)
    hb'.ne).comp x ((hasDerivAt_sin x).const_mul √(3 / 2 : ℝ))
  change HasDerivAt (arcsin ∘ fun y => √(3 / 2 : ℝ) * sin y) _ x
  convert h using 1
  rw [mul_pow, ha]
  ring

/-- The radius is convex up to the extended small-defect endpoint. Its
derivative is compared by squaring positive quantities, avoiding a second
derivative formula at the endpoints. -/
theorem radius_convexOn {b : ℝ} (hb : 0 ≤ b) (hbπ : b ≤ π / 2)
    (ht : sin b ^ 2 ≤ 5 / 12) : ConvexOn ℝ (Icc 0 b) radius := by
  have hsmall (x : ℝ) (hx : x ∈ Icc 0 b) : sin x ^ 2 ≤ 5 / 12 :=
    (sin_sq_mono hx.1 hx.2 hbπ).trans ht
  have hder (x : ℝ) (hx : x ∈ Icc 0 b) := radius_deriv hx.1 (hx.2.trans hbπ) (hsmall x hx)
  apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 b)
    ((continuous_arcsin.comp (continuous_const.mul continuous_sin)).continuousOn)
    (fun x hx => (hder x (interior_subset hx)).differentiableAt.differentiableWithinAt)
  intro x hx y hy hxy
  have hx' := interior_subset hx
  have hy' := interior_subset hy
  change deriv radius x ≤ deriv radius y
  rw [(hder x hx').deriv, (hder y hy').deriv]
  have htx := hsmall x hx'
  have hty := hsmall y hy'
  have hpx : 0 < 1 - (3 / 2 : ℝ) * sin x ^ 2 := by linarith
  have hpy : 0 < 1 - (3 / 2 : ℝ) * sin y ^ 2 := by linarith
  have hcx : 0 ≤ cos x := cos_nonneg_of_mem_Icc ⟨by linarith [hx'.1, pi_pos], hx'.2.trans hbπ⟩
  have hcy : 0 ≤ cos y := cos_nonneg_of_mem_Icc ⟨by linarith [hy'.1, pi_pos], hy'.2.trans hbπ⟩
  apply (div_le_div_iff₀ (sqrt_pos.2 hpx) (sqrt_pos.2 hpy)).2
  rw [mul_assoc, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
  apply le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hcy (sqrt_nonneg _))
  rw [mul_pow, mul_pow, sq_sqrt hpx.le, sq_sqrt hpy.le]
  have hsin := sin_sq_mono hx'.1 hxy (hy'.2.trans hbπ)
  nlinarith only [hsin, sin_sq_add_cos_sq x, sin_sq_add_cos_sq y]

/-- The secant from zero bounds the radius at every smaller defect. -/
theorem radius_le_secant {b δ : ℝ} (hb : 0 < b) (hbπ : b ≤ π / 2)
    (ht : sin b ^ 2 ≤ 5 / 12) (hδ : 0 ≤ δ) (hδb : δ ≤ b) :
    radius δ ≤ (radius b / b) * δ := by
  by_cases hzero : δ = 0
  · simp [hzero, radius]
  have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hzero)
  have h := (radius_convexOn hb.le hbπ ht).secant_mono
    (show 0 ∈ Icc (0 : ℝ) b from ⟨le_rfl, hb.le⟩) ⟨hδ, hδb⟩ ⟨hb.le, le_rfl⟩
    hzero hb.ne' hδb
  simp only [radius, sin_zero, mul_zero, arcsin_zero, sub_zero] at h ⊢
  exact (div_le_iff₀ hδpos).mp h

/-- The crossover for the closed-hemisphere bound. -/
def cutoffFive : ℝ := arccos (1 / 3) / 2

/-- The crossover for the five-point cap bound. -/
def cutoffSix : ℝ := arccos (1 / 6) / 2

theorem cutoffFive_facts : 0 < cutoffFive ∧ cutoffFive ≤ π / 2 ∧
    sin cutoffFive ^ 2 = 1 / 3 ∧ 2 * radius cutoffFive = π / 2 := by
  have hb : 0 < cutoffFive := div_pos (arccos_pos.2 (by norm_num)) (by norm_num)
  have hbπ : cutoffFive ≤ π / 2 := by unfold cutoffFive; linarith [arccos_le_pi (1 / 3 : ℝ)]
  have hc : cos (2 * cutoffFive) = (1 / 3 : ℝ) := by
    rw [cutoffFive, show 2 * (arccos (1 / 3 : ℝ) / 2) = arccos (1 / 3) by ring,
      cos_arccos (by norm_num) (by norm_num)]
  have ht : sin cutoffFive ^ 2 = (1 / 3 : ℝ) := by rw [cos_two_mul_eq_one_sub] at hc; linarith
  obtain ⟨hR, hRπ, hsin, _, _, _⟩ := radius_facts hb.le hbπ (by rw [ht]; norm_num)
  have hcos : cos (2 * radius cutoffFive) = 0 := by
    rw [cos_two_mul_eq_one_sub, hsin, mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 2), ht]
    norm_num
  have h := arccos_cos (show 0 ≤ 2 * radius cutoffFive by linarith)
    (show 2 * radius cutoffFive ≤ π by linarith)
  rw [hcos, arccos_zero] at h
  exact ⟨hb, hbπ, ht, h.symm⟩

theorem cutoffSix_facts : 0 < cutoffSix ∧ cutoffSix ≤ π / 2 ∧
    sin cutoffSix ^ 2 = 5 / 12 ∧ 2 * radius cutoffSix = arccos (-(1 / 4 : ℝ)) := by
  have hb : 0 < cutoffSix := div_pos (arccos_pos.2 (by norm_num)) (by norm_num)
  have hbπ : cutoffSix ≤ π / 2 := by unfold cutoffSix; linarith [arccos_le_pi (1 / 6 : ℝ)]
  have hc : cos (2 * cutoffSix) = (1 / 6 : ℝ) := by
    rw [cutoffSix, show 2 * (arccos (1 / 6 : ℝ) / 2) = arccos (1 / 6) by ring,
      cos_arccos (by norm_num) (by norm_num)]
  have ht : sin cutoffSix ^ 2 = (5 / 12 : ℝ) := by rw [cos_two_mul_eq_one_sub] at hc; linarith
  obtain ⟨hR, hRπ, hsin, _, _, _⟩ := radius_facts hb.le hbπ ht.le
  have hcos : cos (2 * radius cutoffSix) = -(1 / 4 : ℝ) := by
    rw [cos_two_mul_eq_one_sub, hsin, mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 2), ht]
    norm_num
  have h := arccos_cos (show 0 ≤ 2 * radius cutoffSix by linarith)
    (show 2 * radius cutoffSix ≤ π by linarith)
  rw [hcos] at h
  exact ⟨hb, hbπ, ht, h.symm⟩

/-- The trigonometric forms of the extended cutoff agree. -/
theorem cutoffSix_eq_arcsin : cutoffSix = arcsin (√(5 / 12 : ℝ)) := by
  obtain ⟨hb, hbπ, ht, _⟩ := cutoffSix_facts
  have hs : 0 ≤ sin cutoffSix := sin_nonneg_of_nonneg_of_le_pi hb.le (by linarith [pi_pos])
  have he : sin cutoffSix = √(5 / 12 : ℝ) := by rw [← ht, sqrt_sq hs]
  have h := arcsin_sin (by linarith [pi_pos]) hbπ
  rw [he] at h
  exact h.symm

/-- The clique-five coefficient lies strictly below `8/3`. -/
theorem cliqueFive_coefficient_lt : π / arccos (1 / 3 : ℝ) < 8 / 3 := by
  have hcos : (1 / 3 : ℝ) < cos (6 / 5 : ℝ) := by
    have h := (SU2ChordalIntervals.cos_bounds (x := 6 / 5) (by norm_num)
      (by linarith [pi_gt_three]) 1).1
    change (∑ i ∈ Finset.range 4, (-1 : ℝ) ^ i *
      ((6 / 5 : ℝ) ^ (2 * i) / (2 * i).factorial)) ≤ cos (6 / 5 : ℝ) at h
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hac : (6 / 5 : ℝ) < arccos (1 / 3 : ℝ) := by
    have h := arccos_lt_arccos (by norm_num : (-1 : ℝ) ≤ 1 / 3) hcos (cos_le_one _)
    rwa [arccos_cos (by norm_num) (by linarith [pi_gt_three])] at h
  exact (div_lt_iff₀ (arccos_pos.2 (by norm_num))).2 (by linarith [pi_lt_d2])

/-- Rational cosine partial sums certify the strict clique-six comparison. -/
theorem cliqueSix_coefficient_lt :
    2 * arccos (-(1 / 4 : ℝ)) / arccos (1 / 6 : ℝ) < 13 / 5 := by
  have hupper : cos (18235 / 10000 : ℝ) < -(1 / 4 : ℝ) := by
    have h := (SU2ChordalIntervals.cos_bounds (x := 18235 / 10000) (by norm_num)
      (by linarith [pi_gt_three]) 3).2
    change cos (18235 / 10000 : ℝ) ≤ (∑ i ∈ Finset.range 7, (-1 : ℝ) ^ i *
      ((18235 / 10000 : ℝ) ^ (2 * i) / (2 * i).factorial)) at h
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hlower : (1 / 6 : ℝ) < cos (1403 / 1000 : ℝ) := by
    have h := (SU2ChordalIntervals.cos_bounds (x := 1403 / 1000) (by norm_num)
      (by linarith [pi_gt_three]) 2).1
    change (∑ i ∈ Finset.range 6, (-1 : ℝ) ^ i *
      ((1403 / 1000 : ℝ) ^ (2 * i) / (2 * i).factorial)) ≤ cos (1403 / 1000 : ℝ) at h
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hnum : arccos (-(1 / 4 : ℝ)) < 18235 / 10000 := by
    have h := arccos_lt_arccos (neg_one_le_cos _) hupper (by norm_num : -(1 / 4 : ℝ) ≤ 1)
    rwa [arccos_cos (by norm_num) (by linarith [pi_gt_three])] at h
  have hden : (1403 / 1000 : ℝ) < arccos (1 / 6 : ℝ) := by
    have h := arccos_lt_arccos (by norm_num : (-1 : ℝ) ≤ 1 / 6) hlower (cos_le_one _)
    rwa [arccos_cos (by norm_num) (by linarith [pi_gt_three])] at h
  exact (div_lt_iff₀ (arccos_pos.2 (by norm_num))).2 (by linarith)

end Omega.Geometry.SU2Caratheodory
