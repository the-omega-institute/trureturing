/- GID: D5/S3/Estimation/TimeArrow/RectangleCalibrationBounds
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/RectangleCalibrationBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shared calibration variance is controlled uniformly by root tilt and rectangle displacement. -/

import D5.S3.Estimation.TimeArrow.SharedRectangleCalibration

open scoped BigOperators Topology
open Finset Filter
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds
noncomputable section

private theorem sigmoid_variance_formula (x : ℝ) :
    Real.sigmoid x * (1 - Real.sigmoid x) =
      Real.exp (-x) / (1 + Real.exp (-x)) ^ 2 := by
  rw [Real.sigmoid_def]
  field_simp
  <;> ring

/-- A bounded common odds tilt controls every Bernoulli variance by the
same factors, independently of its unshifted score. -/
private theorem sigmoid_variance_tilt (x h : ℝ)
    (hl : 1 / 2 ≤ Real.exp (-h)) (hu : Real.exp (-h) ≤ 2) :
    (Real.sigmoid x * (1 - Real.sigmoid x)) / 2 ≤
        Real.sigmoid (x + h) * (1 - Real.sigmoid (x + h)) ∧
      Real.sigmoid (x + h) * (1 - Real.sigmoid (x + h)) ≤
        2 * (Real.sigmoid x * (1 - Real.sigmoid x)) := by
  rw [sigmoid_variance_formula, sigmoid_variance_formula, neg_add, Real.exp_add]
  let w := Real.exp (-x)
  let z := Real.exp (-h)
  have hw : 0 < w := Real.exp_pos _
  have hz : 0 < z := Real.exp_pos _
  change 1 / 2 ≤ z at hl
  change z ≤ 2 at hu
  change w / (1 + w) ^ 2 / 2 ≤ w * z / (1 + w * z) ^ 2 ∧
    w * z / (1 + w * z) ^ 2 ≤ 2 * (w / (1 + w) ^ 2)
  have hd : 0 < (1 + w) ^ 2 := sq_pos_of_pos (by positivity)
  have he : 0 < (1 + w * z) ^ 2 := sq_pos_of_pos (by positivity)
  constructor
  · rw [div_div, div_le_div_iff₀ (mul_pos hd (by norm_num : (0 : ℝ) < 2)) he]
    have hp : 0 ≤ z * (2 - z) * w ^ 2 :=
      mul_nonneg (mul_nonneg hz.le (by linarith)) (sq_nonneg w)
    nlinarith
  · rw [← mul_div_assoc, div_le_div_iff₀ he hd]
    have hp : 0 ≤ z * (2 * z - 1) * w ^ 2 :=
      mul_nonneg (mul_nonneg hz.le (by linarith)) (sq_nonneg w)
    nlinarith

private theorem sigmoid_variance_bounds (x : ℝ) :
    0 ≤ Real.sigmoid x * (1 - Real.sigmoid x) ∧
      Real.sigmoid x * (1 - Real.sigmoid x) ≤ 1 / 4 := by
  constructor
  · exact mul_nonneg (Real.sigmoid_nonneg x) (sub_nonneg.mpr (Real.sigmoid_le_one x))
  · nlinarith [sq_nonneg (Real.sigmoid x - 1 / 2)]

/-- Changing the same rectangle histogram has a uniform effect on full
variance at a fixed root. The outside rows cancel exactly. -/
private theorem variance_histogram_displacement {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U t t0 x : ℝ) :
    |calibratedVariance outside r ε N R U t x -
      calibratedVariance outside r ε N R U t0 x| ≤ |t - t0| := by
  have hi : calibratedVariance outside r ε N R U t x -
      calibratedVariance outside r ε N R U t0 x =
      (t - t0) * (Real.sigmoid x * (1 - Real.sigmoid x) +
        Real.sigmoid (x + offsets r ε 3) * (1 - Real.sigmoid (x + offsets r ε 3)) -
        Real.sigmoid (x + offsets r ε 1) * (1 - Real.sigmoid (x + offsets r ε 1)) -
        Real.sigmoid (x + offsets r ε 2) * (1 - Real.sigmoid (x + offsets r ε 2))) := by
    simp [calibratedVariance, cellCounts, offsets, Fin.sum_univ_four]
    ring
  rw [hi, abs_mul]
  have hb : |Real.sigmoid x * (1 - Real.sigmoid x) +
        Real.sigmoid (x + offsets r ε 3) * (1 - Real.sigmoid (x + offsets r ε 3)) -
        Real.sigmoid (x + offsets r ε 1) * (1 - Real.sigmoid (x + offsets r ε 1)) -
        Real.sigmoid (x + offsets r ε 2) * (1 - Real.sigmoid (x + offsets r ε 2))| ≤ 1 := by
    apply abs_le.mpr
    have h0 := sigmoid_variance_bounds x
    have h1 := sigmoid_variance_bounds (x + offsets r ε 1)
    have h2 := sigmoid_variance_bounds (x + offsets r ε 2)
    have h3 := sigmoid_variance_bounds (x + offsets r ε 3)
    constructor <;> linarith
  exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (mul_one _)

/-- A bounded root tilt gives uniform full-variance comparison for every
feasible rectangle histogram, including every outside row. -/
private theorem variance_root_tilt {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U t x h : ℝ) (hc : ∀ j, 0 ≤ cellCounts N R U t j)
    (hl : 1 / 2 ≤ Real.exp (-h)) (hu : Real.exp (-h) ≤ 2) :
    calibratedVariance outside r ε N R U t x / 2 ≤
        calibratedVariance outside r ε N R U t (x + h) ∧
      calibratedVariance outside r ε N R U t (x + h) ≤
        2 * calibratedVariance outside r ε N R U t x := by
  have ho (i : ι) := sigmoid_variance_tilt (x + outside i) h hl hu
  have hi (j : Fin 4) := sigmoid_variance_tilt (x + offsets r ε j) h hl hu
  unfold calibratedVariance
  constructor
  · rw [add_div, sum_div, sum_div]
    apply add_le_add
    · apply sum_le_sum
      intro i _
      simpa only [add_assoc, add_comm, add_left_comm] using (ho i).1
    · apply sum_le_sum
      intro j _
      have hh := mul_le_mul_of_nonneg_left (hi j).1 (hc j)
      simpa only [mul_div_assoc, mul_assoc, add_assoc, add_comm, add_left_comm] using hh
  · rw [mul_add, mul_sum, mul_sum]
    apply add_le_add
    · apply sum_le_sum
      intro i _
      simpa only [add_assoc, add_comm, add_left_comm] using (ho i).2
    · apply sum_le_sum
      intro j _
      have hh := mul_le_mul_of_nonneg_left (hi j).2 (hc j)
      simpa only [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using hh

/-- A single base variance controls the entire feasible central rectangle
fiber and a fixed root box. No histogram-dependent neighborhood is used. -/
theorem central_fiber_variance_bounds {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U t t0 x h w : ℝ) (hc : ∀ j, 0 ≤ cellCounts N R U t j)
    (ht : |t - t0| ≤ w) (hl : 1 / 2 ≤ Real.exp (-h)) (hu : Real.exp (-h) ≤ 2) :
    (calibratedVariance outside r ε N R U t0 x - w) / 2 ≤
        calibratedVariance outside r ε N R U t (x + h) ∧
      calibratedVariance outside r ε N R U t (x + h) ≤
        2 * (calibratedVariance outside r ε N R U t0 x + w) := by
  have hd := (abs_le.mp ((variance_histogram_displacement outside r ε N R U t t0 x).trans ht))
  have hb := variance_root_tilt outside r ε N R U t x h hc hl hu
  constructor <;> linarith

private theorem calibration_histogram_displacement {ι : Type*} [Fintype ι]
    (outside : ι → ℝ) (r ε N R U t t0 x : ℝ) :
    |calibratedMean outside r ε N R U t x - calibratedMean outside r ε N R U t0 x| ≤
      2 * |t - t0| := by
  have hi : calibratedMean outside r ε N R U t x -
      calibratedMean outside r ε N R U t0 x = (t - t0) * checkerboard r ε x := by
    simp [calibratedMean, cellCounts, checkerboard, offsets, Fin.sum_univ_four]
    ring
  have hb : |checkerboard r ε x| ≤ 2 := by
    unfold checkerboard
    apply abs_le.mpr
    have h0 := Real.sigmoid_nonneg x
    have h0' := Real.sigmoid_le_one x
    have h1 := Real.sigmoid_nonneg (x + offsets r ε 1)
    have h1' := Real.sigmoid_le_one (x + offsets r ε 1)
    have h2 := Real.sigmoid_nonneg (x + offsets r ε 2)
    have h2' := Real.sigmoid_le_one (x + offsets r ε 2)
    have h3 := Real.sigmoid_nonneg (x + offsets r ε 3)
    have h3' := Real.sigmoid_le_one (x + offsets r ε 3)
    constructor <;> linarith
  rw [hi, abs_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (abs_nonneg (t - t0))

open private
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibratedVariance_pos
from D5.S3.Estimation.TimeArrow.SharedRectangleCalibration

/-- A quantitative bootstrap confines any root of a feasible central
histogram to one fixed box around the base root and bounds its displacement.
The base variance alone supplies the derivative lower bound throughout the
box; it is not a separate uniform-feedback assumption. -/
theorem shared_root_central_bootstrap {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U q t t0 x0 x w : ℝ) (hN : 0 < N)
    (hc : ∀ j, 0 ≤ cellCounts N R U t j) (ht : |t - t0| ≤ w)
    (hbase : calibratedMean outside r ε N R U t0 x0 = q)
    (hroot : calibratedMean outside r ε N R U t x = q)
    (hvar : w < calibratedVariance outside r ε N R U t0 x0)
    (hsmall : 2 * w ≤ (calibratedVariance outside r ε N R U t0 x0 - w) / 2 * Real.log 2) :
    |x - x0| ≤ Real.log 2 ∧
      |x - x0| ≤ 4 * w / (calibratedVariance outside r ε N R U t0 x0 - w) ∧
      (calibratedVariance outside r ε N R U t0 x0 - w) / 2 ≤
        calibratedVariance outside r ε N R U t x ∧
      calibratedVariance outside r ε N R U t x ≤
        2 * (calibratedVariance outside r ε N R U t0 x0 + w) := by
  let d := Real.log (2 : ℝ)
  let a := (calibratedVariance outside r ε N R U t0 x0 - w) / 2
  let F := calibratedMean outside r ε N R U t
  change F x = q at hroot
  have hd : 0 < d := Real.log_pos (by norm_num)
  have ha : 0 < a := by dsimp [a]; linarith
  have htilt (h : ℝ) (hh : |h| ≤ d) :
      1 / 2 ≤ Real.exp (-h) ∧ Real.exp (-h) ≤ 2 := by
    have hb := abs_le.mp hh
    constructor
    · calc
        1 / 2 = Real.exp (-d) := by simp [d, Real.exp_neg, Real.exp_log]
        _ ≤ Real.exp (-h) := Real.exp_le_exp.mpr (by linarith)
    · calc
        Real.exp (-h) ≤ Real.exp d := Real.exp_le_exp.mpr (by linarith)
        _ = 2 := Real.exp_log (by norm_num)
  have hlower (u : ℝ) (hu : u ∈ Set.Icc (x0 - d) (x0 + d)) :
      a ≤ calibratedVariance outside r ε N R U t u := by
    have hh : |u - x0| ≤ d := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hb := central_fiber_variance_bounds outside r ε N R U t t0 x0 (u - x0) w
      hc ht (htilt _ hh).1 (htilt _ hh).2
    simpa only [add_sub_cancel] using hb.1
  have hcont : ContinuousOn F (Set.Icc (x0 - d) (x0 + d)) := by
    exact fun u _ =>
      (D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv
        outside r ε N R U t u).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Set.Icc (x0 - d) (x0 + d))) :=
    fun u _ => (D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv outside r ε N R U t u).differentiableAt.differentiableWithinAt
  have hslope := (convex_Icc (x0 - d) (x0 + d)).mul_sub_le_image_sub_of_le_deriv
    hcont hdiff (fun u hu => by
      rw [(D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv outside r ε N R U t u).deriv]
      exact hlower u (interior_subset hu))
  have h0 : x0 ∈ Set.Icc (x0 - d) (x0 + d) := ⟨by linarith, by linarith⟩
  have hbot : x0 - d ∈ Set.Icc (x0 - d) (x0 + d) := ⟨le_rfl, by linarith⟩
  have htop : x0 + d ∈ Set.Icc (x0 - d) (x0 + d) := ⟨by linarith, le_rfl⟩
  have hdisp : |F x0 - q| ≤ 2 * w := by
    have hh := calibration_histogram_displacement outside r ε N R U t t0 x0
    rw [hbase] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left ht (by norm_num))
  have hdisp' := abs_le.mp hdisp
  have hb := hslope (x0 - d) hbot x0 h0 (by linarith)
  have hu := hslope x0 h0 (x0 + d) htop (by linarith)
  have hmono : StrictMono F := strictMono_of_deriv_pos fun u => by
    rw [(D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv outside r ε N R U t u).deriv]
    exact D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibratedVariance_pos outside r ε N R U t u hN hc
  have hx : x ∈ Set.Icc (x0 - d) (x0 + d) := by
    constructor
    · apply hmono.le_iff_le.mp
      change F (x0 - d) ≤ F x
      rw [hroot]
      dsimp [a, d] at hb ⊢
      nlinarith
    · apply hmono.le_iff_le.mp
      change F x ≤ F (x0 + d)
      rw [hroot]
      dsimp [a, d] at hu ⊢
      nlinarith
  have hbox : |x - x0| ≤ d := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hmotion : a * |x - x0| ≤ 2 * w := by
    by_cases h : x0 ≤ x
    · have hh := hslope x0 h0 x hx h
      rw [hroot] at hh
      rw [abs_of_nonneg (sub_nonneg.mpr h)]
      linarith
    · have hh := hslope x hx x0 h0 (le_of_not_ge h)
      rw [hroot] at hh
      rw [abs_of_nonpos (by linarith : x - x0 ≤ 0)]
      linarith
  have hmove : |x - x0| ≤ 4 * w /
      (calibratedVariance outside r ε N R U t0 x0 - w) := by
    apply (le_div_iff₀ (sub_pos.mpr hvar)).mpr
    dsimp [a] at hmotion
    nlinarith
  have hv := central_fiber_variance_bounds outside r ε N R U t t0 x0 (x - x0) w
    hc ht (htilt _ hbox).1 (htilt _ hbox).2
  simpa only [add_sub_cancel] using And.intro hbox (And.intro hmove hv)

end
end D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds
