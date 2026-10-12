/- GID: D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeSharedRootFeedback
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An actual complete-root anchor controls one central calibration curve and its positive compensated response. -/
import D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
import D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
import D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
import Mathlib.Probability.Distributions.Poisson.Basic
open scoped BigOperators
open Finset ProbabilityTheory
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeReferenceCalibration
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Topology
open Finset Filter
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open private
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibratedVariance_pos
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_lipschitz_certificate
  D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds.sigmoid_variance_bounds
from D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
namespace D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds
noncomputable section
private theorem checkerboard_abs_le_two (r ε x : ℝ) : |checkerboard r ε x| ≤ 2 := by
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
private theorem calibration_histogram_displacement {ι : Type*} [Fintype ι]
    (outside : ι → ℝ) (r ε N R U t t0 x : ℝ) :
    |calibratedMean outside r ε N R U t x - calibratedMean outside r ε N R U t0 x| ≤
      2 * |t - t0| := by
  have hi : calibratedMean outside r ε N R U t x -
      calibratedMean outside r ε N R U t0 x = (t - t0) * checkerboard r ε x := by
    simp [calibratedMean, cellCounts, checkerboard, offsets, Fin.sum_univ_four]; ring
  have hb := checkerboard_abs_le_two r ε x
  rw [hi, abs_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (abs_nonneg (t - t0))
/-- A positive derivative on a fixed box turns a center residual into
an explicit displacement bound for any root of the same equation. -/
theorem root_box_of_residual (F : ℝ → ℝ) (q x0 x d a b : ℝ)
    (hd : 0 < d) (ha : 0 < a) (hmono : StrictMono F)
    (hcont : ContinuousOn F (Set.Icc (x0 - d) (x0 + d)))
    (hdiff : DifferentiableOn ℝ F (interior (Set.Icc (x0 - d) (x0 + d))))
    (hlower : ∀ u ∈ interior (Set.Icc (x0 - d) (x0 + d)), a ≤ deriv F u)
    (hroot : F x = q) (hres : |F x0 - q| ≤ b) (hsmall : b ≤ a * d) :
    |x - x0| ≤ d ∧ a * |x - x0| ≤ b := by
  have hslope := (convex_Icc (x0 - d) (x0 + d)).mul_sub_le_image_sub_of_le_deriv hcont hdiff hlower
  have h0 : x0 ∈ Set.Icc (x0 - d) (x0 + d) := ⟨by linarith, by linarith⟩
  have hbot : x0 - d ∈ Set.Icc (x0 - d) (x0 + d) := ⟨le_rfl, by linarith⟩
  have htop : x0 + d ∈ Set.Icc (x0 - d) (x0 + d) := ⟨by linarith, le_rfl⟩
  have hres' := abs_le.mp hres
  have hb := hslope (x0 - d) hbot x0 h0 (by linarith)
  have hu := hslope x0 h0 (x0 + d) htop (by linarith)
  have hx : x ∈ Set.Icc (x0 - d) (x0 + d) := by
    constructor
    · apply hmono.le_iff_le.mp
      rw [hroot]; nlinarith only [hb, hsmall, hres'.1, hres'.2]
    · apply hmono.le_iff_le.mp
      rw [hroot]; nlinarith only [hu, hsmall, hres'.1, hres'.2]
  refine ⟨abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
  by_cases h : x0 ≤ x
  · have hh := hslope x0 h0 x hx h
    rw [hroot] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith only [hh, hres'.1]
  · have hh := hslope x hx x0 h0 (le_of_not_ge h)
    rw [hroot] at hh
    rw [abs_of_nonpos (by linarith : x - x0 ≤ 0)]; linarith only [hh, hres'.2]
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
    · calc Real.exp (-h) ≤ Real.exp d := Real.exp_le_exp.mpr (by linarith) _ = 2 := Real.exp_log (by norm_num)
  have hlower (u : ℝ) (hu : u ∈ Set.Icc (x0 - d) (x0 + d)) :
      a ≤ calibratedVariance outside r ε N R U t u := by
    have hh : |u - x0| ≤ d := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hb := central_fiber_variance_bounds outside r ε N R U t t0 x0 (u - x0) w hc ht (htilt _ hh).1 (htilt _ hh).2
    simpa only [add_sub_cancel] using hb.1
  have hcont : ContinuousOn F (Set.Icc (x0 - d) (x0 + d)) := by
    exact fun u _ =>
      (D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv
        outside r ε N R U t u).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Set.Icc (x0 - d) (x0 + d))) :=
    fun u _ => (D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv outside r ε N R U t u).differentiableAt.differentiableWithinAt
  have hdisp : |F x0 - q| ≤ 2 * w := by
    have hh := calibration_histogram_displacement outside r ε N R U t t0 x0
    rw [hbase] at hh; exact hh.trans (mul_le_mul_of_nonneg_left ht (by norm_num))
  have hmono : StrictMono F := strictMono_of_deriv_pos fun u => by
    rw [(D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv outside r ε N R U t u).deriv]
    exact D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibratedVariance_pos outside r ε N R U t u hN hc
  have hb := root_box_of_residual F q x0 x d a (2 * w) hd ha hmono hcont hdiff
    (fun u hu => by
      rw [(D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv outside r ε N R U t u).deriv]
      exact hlower u (interior_subset hu)) hroot hdisp hsmall
  have hbox := hb.1
  have hmotion := hb.2
  have hmove : |x - x0| ≤ 4 * w /
      (calibratedVariance outside r ε N R U t0 x0 - w) := by
    apply (le_div_iff₀ (sub_pos.mpr hvar)).mpr
    dsimp [a] at hmotion; nlinarith
  have hv := central_fiber_variance_bounds outside r ε N R U t t0 x0 (x - x0) w hc ht (htilt _ hbox).1 (htilt _ hbox).2
  simpa only [add_sub_cancel] using And.intro hbox (And.intro hmove hv)
/-- Quantitative feedback in a common compensated root box. Its size is
controlled by the same full variance, rather than an independent denominator. -/
theorem compensated_feedback_bounds (r ε x B D d a b X : ℝ)
    (ha : 0 < a) (haD : a ≤ D) (hDb : D ≤ b)
    (hB : 0 ≤ B) (hd : 0 ≤ d) (hneg : checkerboard r ε x ≤ -d)
    (hx : |x| ≤ X) (hbox : |x| ≤ Real.log 2) :
    B * d / (8 * b) - X / 4 ≤
      Real.sigmoid x - 1 / 2 -
        B * Real.sigmoid x * (1 - Real.sigmoid x) * checkerboard r ε x / D ∧
      Real.sigmoid x - 1 / 2 -
        B * Real.sigmoid x * (1 - Real.sigmoid x) * checkerboard r ε x / D ≤
          X / 4 + B / (2 * a) := by
  have hD : 0 < D := lt_of_lt_of_le ha haD
  have hb : 0 < b := lt_of_lt_of_le hD hDb
  have ht : 1 / 2 ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ 2 := by
    have hh := abs_le.mp hbox
    constructor
    · calc
        1 / 2 = Real.exp (-Real.log (2 : ℝ)) := by simp [Real.exp_neg, Real.exp_log]
        _ ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    · calc Real.exp (-x) ≤ Real.exp (Real.log (2 : ℝ)) := Real.exp_le_exp.mpr (by linarith) _ = 2 := Real.exp_log (by norm_num)
  have hv : 1 / 8 ≤ Real.sigmoid x * (1 - Real.sigmoid x) := by
    have hh := (sigmoid_variance_tilt 0 x ht.1 ht.2).1
    norm_num [Real.sigmoid_def] at hh
    simpa [Real.sigmoid_def] using hh
  have hvu := (sigmoid_variance_bounds x).2
  have hp := (sigmoid_variance_bounds x).1
  have hn : d ≤ -checkerboard r ε x := by linarith
  have hnu : -checkerboard r ε x ≤ 2 := by
    have hh := abs_le.mp (checkerboard_abs_le_two r ε x)
    linarith
  have hs : |Real.sigmoid x - 1 / 2| ≤ X / 4 := by
    have hh := D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_lipschitz_certificate.dist_le_mul x 0
    norm_num [Real.dist_eq, Real.sigmoid_def] at hh; exact hh.trans (by linarith)
  have hl : B * d / (8 * b) ≤
      B * (Real.sigmoid x * (1 - Real.sigmoid x)) * (-checkerboard r ε x) / D := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * b) hD).mpr
    have h1 := mul_le_mul hv hn hd hp
    have h2 := mul_le_mul_of_nonneg_left h1 hB
    have h3 := mul_le_mul_of_nonneg_left hDb (mul_nonneg hB hd)
    have h4 := mul_le_mul_of_nonneg_left h2 hb.le
    nlinarith
  have hu : B * (Real.sigmoid x * (1 - Real.sigmoid x)) * (-checkerboard r ε x) / D ≤
      B / (2 * a) := by
    apply (div_le_div_iff₀ hD (by positivity : (0 : ℝ) < 2 * a)).mpr
    have h1 := mul_le_mul hvu hnu (by linarith : 0 ≤ -checkerboard r ε x) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have h2 := mul_le_mul_of_nonneg_left h1 hB
    have h3 := mul_le_mul_of_nonneg_left haD hB
    have h4 := mul_le_mul_of_nonneg_left h2 ha.le
    nlinarith
  have he : Real.sigmoid x - 1 / 2 - B * Real.sigmoid x * (1 - Real.sigmoid x) * checkerboard r ε x / D = Real.sigmoid x - 1 / 2 +
          B * (Real.sigmoid x * (1 - Real.sigmoid x)) * (-checkerboard r ε x) / D := by ring
  rw [he]
  constructor <;> linarith [abs_le.mp hs]
/-- One rectangle-independent compensated root box works for every
outside histogram and both native experiments. -/
theorem compensated_feedback_box {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ d δ : ℝ, 0 < d ∧ 0 < δ ∧ δ ≤ Real.log 2 ∧
      ∀ ε x : ℝ, |ε| < δ → |x| < δ → checkerboard r ε x ≤ -d := by
  obtain ⟨d, hd, hh⟩ := checkerboard_negative_neighborhood hr hr1
  obtain ⟨η, hη, he⟩ := Metric.eventually_nhds_iff.mp hh
  refine ⟨d, min η (Real.log 2), hd, lt_min hη (Real.log_pos (by norm_num)), min_le_right _ _, ?_⟩
  intro ε x hε hx
  apply le_of_lt
  apply he (y := (ε, x))
  simpa only [Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff] using
    And.intro (hε.trans_le (min_le_left _ _)) (hx.trans_le (min_le_left _ _))
end
end D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds
namespace D5.S3.Estimation.TimeArrow.NativeReferenceVarianceBounds
noncomputable section
private theorem poisson_atom_lower (mu : ℝ) (hmu : 0 < mu) {n : ℕ} (hn : 0 < n) :
    Real.exp (-((n : ℝ) - mu) ^ 2 / mu - 1) / Real.sqrt n ≤
      Real.exp (-mu) * mu ^ n / n.factorial := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmuR : (0 : ℝ) < mu := hmu
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hs := (D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge.log_factorial_envelopes hn).2
  have hl := Real.log_le_sub_one_of_pos (div_pos hnR hmuR)
  rw [Real.log_div hnR.ne' hmuR.ne'] at hl
  have he : (n : ℝ) * ((n : ℝ) / mu - 1) - n + mu = ((n : ℝ) - mu) ^ 2 / mu := by
    field_simp <;> ring
  have hh := mul_le_mul_of_nonneg_left hl hnR.le
  have hrate : (n : ℝ) * (Real.log n - Real.log mu) - n + mu ≤
      ((n : ℝ) - mu) ^ 2 / mu := by linarith only [hh, he]
  have hp : 0 < Real.exp (-(mu : ℝ)) * (mu : ℝ) ^ n / n.factorial := by positivity
  have hlog : -((n : ℝ) - mu) ^ 2 / mu - 1 - Real.log n / 2 ≤
      Real.log (Real.exp (-(mu : ℝ)) * (mu : ℝ) ^ n / n.factorial) := by
    rw [Real.log_div (by positivity) hf.ne', Real.log_mul (Real.exp_pos _).ne' (pow_pos hmuR n).ne', Real.log_exp, Real.log_pow]
    rw [mul_sub] at hrate; simp only [neg_div] at hrate ⊢
    linarith only [hs, hrate]
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hp] at hexp
  calc
    _ = Real.exp (-((n : ℝ) - mu) ^ 2 / mu - 1 - Real.log n / 2) := by
      rw [← Real.log_sqrt hnR.le, Real.exp_sub (-((n : ℝ) - mu) ^ 2 / mu - 1) (Real.log (Real.sqrt n)),
        Real.exp_log (Real.sqrt_pos.mpr hnR)]
    _ ≤ _ := hexp
private theorem poisson_window_lower (c K lam : ℝ) (hc : 0 < c) (hK : 0 ≤ K)
    (hlam : 0 < lam) {n : ℕ} (hn : 0 < n) (hwindow : |(n : ℝ) - c * lam| ≤ K * Real.sqrt lam)
    (hupper : (n : ℝ) ≤ (3 / 2) * c * lam) :
    Real.exp (-K ^ 2 / c - 1) / (Real.sqrt ((3 / 2) * c) * Real.sqrt lam) ≤
      Real.exp (-(c * lam)) * (c * lam) ^ n / n.factorial := by
  have hmu : 0 < c * lam := mul_pos hc hlam
  have hbase := poisson_atom_lower (c * lam) hmu hn
  have hsq : ((n : ℝ) - c * lam) ^ 2 ≤ K ^ 2 * lam := by
    have hh := mul_self_le_mul_self (abs_nonneg ((n : ℝ) - c * lam)) hwindow
    have hs := Real.sq_sqrt hlam.le
    rw [← pow_two, sq_abs] at hh; nlinarith only [hh, hs]
  have hr : ((n : ℝ) - c * lam) ^ 2 / (c * lam) ≤ K ^ 2 / c := by
    apply (div_le_iff₀ (mul_pos hc hlam)).mpr
    have he : K ^ 2 / c * (c * lam) = K ^ 2 * lam := by field_simp
    rw [he]; exact hsq
  have hnum : Real.exp (-K ^ 2 / c - 1) ≤ Real.exp (-((n : ℝ) - c * lam) ^ 2 / (c * lam) - 1) := Real.exp_le_exp.mpr (by
      simpa only [neg_div] using sub_le_sub_right (neg_le_neg hr) 1)
  have hden : Real.sqrt n ≤ Real.sqrt ((3 / 2) * c) * Real.sqrt lam := by
    rw [← Real.sqrt_mul (by positivity)]; exact Real.sqrt_le_sqrt hupper
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact (div_le_div₀ (Real.exp_pos _).le hnum (Real.sqrt_pos.mpr hnR) hden).trans hbase
open private
  D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_weighted_tail
from D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
open private
  D5.S3.Estimation.TimeArrow.NativeReferenceCalibration.all_row_reference_sum
from D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
/-- Any finite signal count window below the calibration threshold gives a
lower bound for the complete reference variance; all other rows remain in it. -/
theorem reference_variance_count_window {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L) (hq : 1 ≤ q) (hqm : q < M)
    (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val)
    (D : Finset (ℕ × ℕ)) (hD : ∀ c ∈ D, referenceParameter M q r c ≤ 1 / 2) :
    (q : ℝ) / 2 * (∑ c ∈ D, rowReference S r L i c) ≤
      (q : ℝ) * (∑' c, (referenceParameter M q r c * (1 - referenceParameter M q r c)) *
        rowReference S r L i c) +
      ((M - q : ℕ) : ℝ) * (∑' c, (referenceParameter M q r c * (1 - referenceParameter M q r c)) *
        rowReference S r L j c) := by
  have hcal := (reference_calibration_mean_variance S r κ hκ hr hrκ hcκ hL hq hqm i j hi hj).2
  rw [hcal]
  have hqR : (0 : ℝ) ≤ q := by positivity
  have hg (c : ℕ × ℕ) : 0 ≤ 1 - referenceParameter M q r c ∧
      1 - referenceParameter M q r c ≤ 1 := by
    have hp := Real.sigmoid_nonneg (c.1 * Real.log ((1 + r) / (1 - compensation M q r)) +
      c.2 * Real.log ((1 - r) / (1 + compensation M q r)) - Real.log (((M - q : ℕ) : ℝ) / q))
    have hp1 := Real.sigmoid_le_one (c.1 * Real.log ((1 + r) / (1 - compensation M q r)) +
      c.2 * Real.log ((1 - r) / (1 + compensation M q r)) - Real.log (((M - q : ℕ) : ℝ) / q))
    change 0 ≤ referenceParameter M q r c at hp
    change referenceParameter M q r c ≤ 1 at hp1
    constructor <;> linarith only [hp, hp1]
  have hs := (D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_weighted_tail
    S r κ hκ hr hrκ hcκ hL i (fun c => 1 - referenceParameter M q r c) hg).1
  have hsum := hs.sum_le_tsum D (fun c _ => mul_nonneg (hg c).1
    (D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos S r κ hκ hr hrκ hcκ hL i c).le)
  have hl : (1 / 2) * (∑ c ∈ D, rowReference S r L i c) ≤
      ∑ c ∈ D, (1 - referenceParameter M q r c) * rowReference S r L i c := by
    rw [mul_sum]
    apply sum_le_sum
    intro c hc
    exact mul_le_mul_of_nonneg_right (by linarith [hD c hc])
      (D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos S r κ hκ hr hrκ hcκ hL i c).le
  have hh := mul_le_mul_of_nonneg_left (hl.trans hsum) hqR
  simpa only [div_eq_mul_inv, mul_assoc, one_mul] using hh
/-- The two signal Poisson coordinates supply an explicit mass for every
finite rectangle contained in a square-root window. -/
theorem signal_rectangle_mass_lower {M q L : ℕ} (S : Support M q)
    (r K : ℝ) (hr : 0 < r) (hr1 : r < 1) (hK : 0 ≤ K) (hL : 1 ≤ L)
    (i : Fin M) (hi : i ∈ S.val) (D : Finset (ℕ × ℕ))
    (hD : ∀ c ∈ D, 0 < c.1 ∧ 0 < c.2 ∧
      |(c.1 : ℝ) - ((1 + r) / 2) * L| ≤ K * Real.sqrt L ∧
      |(c.2 : ℝ) - ((1 - r) / 2) * L| ≤ K * Real.sqrt L ∧
      (c.1 : ℝ) ≤ (3 / 2) * ((1 + r) / 2) * L ∧
      (c.2 : ℝ) ≤ (3 / 2) * ((1 - r) / 2) * L) :
    (D.card : ℝ) *
      (Real.exp (-K ^ 2 / ((1 + r) / 2) - 1) *
        Real.exp (-K ^ 2 / ((1 - r) / 2) - 1) /
        (Real.sqrt ((3 / 2) * ((1 + r) / 2)) *
          Real.sqrt ((3 / 2) * ((1 - r) / 2)) * L)) ≤
      ∑ c ∈ D, rowReference S r L i c := by
  have hlam : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have ha : 0 < (1 + r) / 2 := by linarith
  have hb : 0 < (1 - r) / 2 := by linarith
  rw [← nsmul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro c hc
  obtain ⟨hn, hm, hw, hv, hu, hz⟩ := hD c hc
  have hp := poisson_window_lower ((1 + r) / 2) K L ha hK hlam hn hw hu
  have hq := poisson_window_lower ((1 - r) / 2) K L hb hK hlam hm hv hz
  have hh := mul_le_mul hp hq (by positivity) (by positivity)
  have hs := Real.sq_sqrt hlam.le
  have hd : (Real.sqrt ((3 / 2) * ((1 + r) / 2)) * Real.sqrt L) * (Real.sqrt ((3 / 2) * ((1 - r) / 2)) * Real.sqrt L) =
      Real.sqrt ((3 / 2) * ((1 + r) / 2)) *
        Real.sqrt ((3 / 2) * ((1 - r) / 2)) * L := by
    calc
      _ = (Real.sqrt ((3 / 2) * ((1 + r) / 2)) *
        Real.sqrt ((3 / 2) * ((1 - r) / 2))) * (Real.sqrt L) ^ 2 := by ring
      _ = _ := by rw [hs]
  rw [← mul_div_mul_comm, hd] at hh
  rw [show ((1 + r) / 2) * (L : ℝ) = (L : ℝ) * (1 + r) / 2 by ring,
    show ((1 - r) / 2) * (L : ℝ) = (L : ℝ) * (1 - r) / 2 by ring] at hh
  unfold rowReference; simp only [b, if_pos hi]
  exact hh
/-- A finite signal square-root window supplies the full reference variance
with no deletion of the remaining signal or background counts. -/
theorem reference_variance_window_lower {M q L : ℕ} (S : Support M q) (r κ K : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L) (hq : 1 ≤ q) (hqm : q < M)
    (hK : 0 ≤ K) (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val)
    (D : Finset (ℕ × ℕ))
    (hwindow : ∀ c ∈ D, 0 < c.1 ∧ 0 < c.2 ∧
      |(c.1 : ℝ) - ((1 + r) / 2) * L| ≤ K * Real.sqrt L ∧
      |(c.2 : ℝ) - ((1 - r) / 2) * L| ≤ K * Real.sqrt L ∧
      (c.1 : ℝ) ≤ (3 / 2) * ((1 + r) / 2) * L ∧
      (c.2 : ℝ) ≤ (3 / 2) * ((1 - r) / 2) * L)
    (hscore : ∀ c ∈ D, referenceParameter M q r c ≤ 1 / 2) :
    (q : ℝ) / 2 * (D.card : ℝ) *
      (Real.exp (-K ^ 2 / ((1 + r) / 2) - 1) *
        Real.exp (-K ^ 2 / ((1 - r) / 2) - 1) /
        (Real.sqrt ((3 / 2) * ((1 + r) / 2)) *
          Real.sqrt ((3 / 2) * ((1 - r) / 2)) * L)) ≤
      (q : ℝ) * (∑' c, (referenceParameter M q r c * (1 - referenceParameter M q r c)) *
        rowReference S r L i c) +
      ((M - q : ℕ) : ℝ) * (∑' c, (referenceParameter M q r c * (1 - referenceParameter M q r c)) *
        rowReference S r L j c) := by
  have hm := signal_rectangle_mass_lower S r K hr (by linarith) hK hL i hi D hwindow
  have hv := reference_variance_count_window S r κ hκ hr hrκ hcκ hL hq hqm i j hi hj D hscore
  have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ (q : ℝ) / 2 by positivity)
  apply le_trans _ hv
  simpa only [mul_assoc] using hh
private theorem natural_interval_card_lower (lo hi t : ℝ) (hlo : 0 ≤ lo)
    (ht : 2 ≤ t) (hwidth : hi - lo = t) :
    t / 2 ≤ ((Icc ⌈lo⌉₊ ⌊hi⌋₊).card : ℝ) := by
  have ha := Nat.ceil_lt_add_one hlo
  have hb := Nat.sub_one_lt_floor hi
  have habR : (⌈lo⌉₊ : ℝ) ≤ ⌊hi⌋₊ := by linarith only [ha, hb, ht, hwidth]
  have hab : ⌈lo⌉₊ ≤ ⌊hi⌋₊ := by exact_mod_cast habR
  rw [Nat.card_Icc, Nat.cast_sub (by omega : ⌈lo⌉₊ ≤ ⌊hi⌋₊ + 1), Nat.cast_add, Nat.cast_one]
  linarith only [ha, hb, ht, hwidth]
/-- A concrete lower-left, upper-right count box gives a linear lower bound
for the complete reference variance. All scale and score conditions are
finite inequalities in the original compensated parameters. -/
theorem reference_linear_variance_lower {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 4 ≤ L) (hq : 1 ≤ q) (hqm : q < M)
    (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val)
    (hplus : 4 * Real.sqrt L ≤ ((1 + r) / 2) * L)
    (hminus : 4 * Real.sqrt L ≤ ((1 - r) / 2) * L)
    (hcenter :
      (((1 + r) / 2) * L) * Real.log ((1 + r) / (1 - compensation M q r)) +
      (((1 - r) / 2) * L) * Real.log ((1 - r) / (1 + compensation M q r)) -
        Real.log (((M - q : ℕ) : ℝ) / q) ≤
      Real.sqrt L * (Real.log ((1 + r) / (1 - compensation M q r)) -
        Real.log ((1 - r) / (1 + compensation M q r)))) :
    (q : ℝ) / 8 *
      (Real.exp (-(2 : ℝ) ^ 2 / ((1 + r) / 2) - 1) *
        Real.exp (-(2 : ℝ) ^ 2 / ((1 - r) / 2) - 1) /
        (Real.sqrt ((3 / 2) * ((1 + r) / 2)) *
          Real.sqrt ((3 / 2) * ((1 - r) / 2)))) ≤
      ∑ k : Fin M, ∑' c, (referenceParameter M q r c * (1 - referenceParameter M q r c)) *
        rowReference S r L k c := by
  classical
  let t := Real.sqrt (L : ℝ)
  let a := ((1 + r) / 2) * L
  let b := ((1 - r) / 2) * L
  let A := Icc ⌈a - 2 * t⌉₊ ⌊a - t⌋₊
  let B := Icc ⌈b + t⌉₊ ⌊b + 2 * t⌋₊
  let D := A ×ˢ B
  have hLam : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have ht : 2 ≤ t := by
    dsimp [t]
    have hh : Real.sqrt (4 : ℝ) ≤ Real.sqrt L := Real.sqrt_le_sqrt (by exact_mod_cast hL)
    norm_num at hh ⊢; exact hh
  have ht0 : 0 ≤ t := by positivity
  have hsq : t ^ 2 = L := Real.sq_sqrt hLam.le
  have ha : 4 * t ≤ a := hplus
  have hb : 4 * t ≤ b := hminus
  have hcardA := natural_interval_card_lower (a - 2 * t) (a - t) t (by linarith only [ha, ht]) ht (by ring)
  have hcardB := natural_interval_card_lower (b + t) (b + 2 * t) t (by linarith only [hb, ht]) ht (by ring)
  have hcard : (L : ℝ) / 4 ≤ D.card := by
    dsimp [D]
    rw [card_product, Nat.cast_mul]
    have hh := mul_le_mul hcardA hcardB (by positivity) (by positivity)
    nlinarith only [hh, hsq]
  have hwindow (c : ℕ × ℕ) (hc : c ∈ D) : a - 2 * t ≤ c.1 ∧ (c.1 : ℝ) ≤ a - t ∧
      b + t ≤ c.2 ∧ (c.2 : ℝ) ≤ b + 2 * t := by
    have hh := mem_product.mp hc
    have hp := mem_Icc.mp hh.1
    have hm := mem_Icc.mp hh.2
    have hp1 : (⌈a - 2 * t⌉₊ : ℝ) ≤ c.1 := by exact_mod_cast hp.1
    have hp2 : (c.1 : ℝ) ≤ ⌊a - t⌋₊ := by exact_mod_cast hp.2
    have hm1 : (⌈b + t⌉₊ : ℝ) ≤ c.2 := by exact_mod_cast hm.1
    have hm2 : (c.2 : ℝ) ≤ ⌊b + 2 * t⌋₊ := by exact_mod_cast hm.2
    exact ⟨(Nat.le_ceil _).trans hp1, hp2.trans (Nat.floor_le (by linarith only [ha, ht])), (Nat.le_ceil _).trans hm1,
      hm2.trans (Nat.floor_le (by linarith only [hb, ht]))⟩
  have hw (c : ℕ × ℕ) (hc : c ∈ D) : 0 < c.1 ∧ 0 < c.2 ∧
      |(c.1 : ℝ) - ((1 + r) / 2) * L| ≤ 2 * Real.sqrt L ∧
      |(c.2 : ℝ) - ((1 - r) / 2) * L| ≤ 2 * Real.sqrt L ∧
      (c.1 : ℝ) ≤ (3 / 2) * ((1 + r) / 2) * L ∧
      (c.2 : ℝ) ≤ (3 / 2) * ((1 - r) / 2) * L := by
    obtain ⟨hp, hp', hm, hm'⟩ := hwindow c hc
    have hn : (0 : ℝ) < c.1 := by linarith only [hp, ha, ht]
    have hm0 : (0 : ℝ) < c.2 := by linarith only [hm, hb, ht]
    refine ⟨by exact_mod_cast hn, by exact_mod_cast hm0, ?_, ?_, ?_, ?_⟩
    · apply abs_le.mpr
      change - (2 * t) ≤ (c.1 : ℝ) - a ∧ (c.1 : ℝ) - a ≤ 2 * t
      constructor <;> linarith only [hp, hp', ht]
    · apply abs_le.mpr
      change - (2 * t) ≤ (c.2 : ℝ) - b ∧ (c.2 : ℝ) - b ≤ 2 * t
      constructor <;> linarith only [hm, hm', ht]
    · simp only [mul_assoc]
      change (c.1 : ℝ) ≤ (3 / 2) * a; linarith only [hp', ha, ht]
    · simp only [mul_assoc]
      change (c.2 : ℝ) ≤ (3 / 2) * b; linarith only [hm', hb]
  have hr1 : r < 1 := by linarith only [hrκ, hκ]
  have he : 0 ≤ compensation M q r := by unfold compensation; positivity
  have he1 : compensation M q r < 1 := by linarith only [hcκ, hκ]
  have hu : 0 ≤ Real.log ((1 + r) / (1 - compensation M q r)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (by linarith only [he1])).mpr
    linarith only [hr, he]
  have hv : Real.log ((1 - r) / (1 + compensation M q r)) ≤ 0 := by
    apply Real.log_nonpos (by positivity)
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hr, he]
  have hp (c : ℕ × ℕ) (hc : c ∈ D) : referenceParameter M q r c ≤ 1 / 2 := by
    obtain ⟨_, hk, hl, _⟩ := hwindow c hc
    have hx := mul_le_mul_of_nonneg_right hk hu
    have hy := mul_le_mul_of_nonpos_right hl hv
    unfold referenceParameter
    have hscore : (c.1 : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
        (c.2 : ℝ) * Real.log ((1 - r) / (1 + compensation M q r)) -
        Real.log (((M - q : ℕ) : ℝ) / q) ≤ 0 := by
      dsimp [a, b, t] at hx hy; nlinarith only [hx, hy, hcenter]
    have hh := Real.sigmoid_le hscore
    simpa only [Real.sigmoid_zero, one_div] using hh
  have hbound := reference_variance_window_lower S r κ 2 hκ hr hrκ hcκ (by omega) hq hqm (by norm_num) i j hi hj D hw hp
  rw [← D5.S3.Estimation.TimeArrow.NativeReferenceCalibration.all_row_reference_sum
      S r (fun c => referenceParameter M q r c * (1 - referenceParameter M q r c)) i j hi hj] at hbound
  apply le_trans _ hbound
  have hh := mul_le_mul_of_nonneg_left hcard (show 0 ≤ (q : ℝ) / 2 by positivity)
  have hC : 0 ≤ Real.exp (-(2 : ℝ) ^ 2 / ((1 + r) / 2) - 1) * Real.exp (-(2 : ℝ) ^ 2 / ((1 - r) / 2) - 1) /
      (Real.sqrt ((3 / 2) * ((1 + r) / 2)) * Real.sqrt ((3 / 2) * ((1 - r) / 2)) * L) := by positivity
  have hmult := mul_le_mul_of_nonneg_right hh hC
  convert hmult using 1 <;> field_simp <;> ring
end
end D5.S3.Estimation.TimeArrow.NativeReferenceVarianceBounds
open Finset
open D5.S3.Estimation.TimeArrow.NativeReferenceVarianceBounds
open D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios
namespace D5.S3.Estimation.TimeArrow.NativeRectangleReferenceMass
noncomputable section
private theorem poisson_atom_upper (mu : ℝ) (hmu : 0 < mu) {n : ℕ} (hn : 0 < n) :
    Real.exp (-mu) * mu ^ n / n.factorial ≤ 1 / Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hs := (D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge.log_factorial_envelopes hn).1
  have hl := Real.log_le_sub_one_of_pos (div_pos hmu hnR)
  rw [Real.log_div hmu.ne' hnR.ne'] at hl
  have hh := mul_le_mul_of_nonneg_left hl hnR.le
  have he : (n : ℝ) * (mu / n - 1) = mu - n := by field_simp
  rw [he] at hh
  have hp : 0 < Real.exp (-mu) * mu ^ n / n.factorial := by positivity
  have hlog : Real.log (Real.exp (-mu) * mu ^ n / n.factorial) ≤ -Real.log n / 2 := by
    rw [Real.log_div (by positivity) hf.ne', Real.log_mul (Real.exp_pos _).ne' (pow_pos hmu n).ne', Real.log_exp, Real.log_pow]
    linarith only [hs,hh]
  have hx := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hp] at hx
  calc
    _ ≤ Real.exp (-Real.log n / 2) := hx
    _ = 1 / Real.sqrt n := by
      rw [show -Real.log (n : ℝ) / 2 = -(Real.log (n : ℝ) / 2) by ring,
        Real.exp_neg, ← Real.log_sqrt hnR.le, Real.exp_log (Real.sqrt_pos.mpr hnR)]
      simp only [one_div]
/-- Both bounds refer to k=floor(a lambda), l=lambda-k in the original
signal reference law. In particular q times this mass has scale q/lambda. -/
theorem floored_signal_reference_mass {M q L : ℕ} (S : Support M q)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (hL : 1 ≤ L)
    (i : Fin M) (hi : i ∈ S.val)
    (hplus : 15 ≤ ((1 + r) / 2) * (L : ℝ))
    (hminus : 30 ≤ ((1 - r) / 2) * (L : ℝ)) :
    let a := (1 + r) / 2
    let b := (1 - r) / 2
    let k := ⌊a * (L : ℝ)⌋₊
    let l := L-k
    Real.exp (-1/a-1) * Real.exp (-1/b-1) /
        (Real.sqrt ((3/2)*a) * Real.sqrt ((3/2)*b) * L) ≤ rowReference S r L i (k,l) ∧
      rowReference S r L i (k,l) ≤ 2 / (Real.sqrt (a*b) * L) := by
  classical
  let a := (1 + r) / 2
  let b := (1 - r) / 2
  let k := ⌊a * (L : ℝ)⌋₊
  let l := L-k
  have ha : 0 < a := by dsimp [a]; linarith only [hr]
  have hb : 0 < b := by dsimp [b]; linarith only [hr1]
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hab : a+b=1 := by dsimp [a,b]; ring
  change 15 ≤ a*(L : ℝ) at hplus
  change 30 ≤ b*(L : ℝ) at hminus
  have hround := original_count_rounding r L hr hr1 hL hplus hminus
  dsimp only at hround
  have hkL : k ≤ L := hround.1
  have hk : 0 < k := hround.2.1
  have hl : 0 < l := hround.2.2.1
  have hklo : (k : ℝ) ≤ a*L := Nat.floor_le (by positivity)
  have hkhi : a*(L : ℝ) < k+1 := Nat.lt_floor_add_one _
  have hlr : (l : ℝ) = (L : ℝ)-k := Nat.cast_sub hkL
  have hll : b*(L : ℝ) ≤ l := by rw [hlr]; nlinarith only [hklo,hab]
  have hlu : (l : ℝ) ≤ b*L+1 := by rw [hlr]; nlinarith only [hkhi,hab]
  have hs : (1 : ℝ) ≤ Real.sqrt L := by exact Real.one_le_sqrt.mpr hLR
  dsimp only
  constructor
  · have hm := signal_rectangle_mass_lower S r 1 hr hr1 (by norm_num) hL i hi {(k,l)} (by
        intro c hc
        simp only [mem_singleton] at hc
        subst c
        refine ⟨hk,hl,?_,?_,?_,?_⟩
        · change |(k : ℝ)-a*L| ≤ 1*Real.sqrt L
          rw [abs_le]
          constructor <;> nlinarith only [hklo,hkhi,hs]
        · change |(l : ℝ)-b*L| ≤ 1*Real.sqrt L
          rw [abs_le]
          constructor <;> nlinarith only [hll,hlu,hs]
        · change (k : ℝ) ≤ 3/2*a*L
          nlinarith only [hklo,hplus]
        · change (l : ℝ) ≤ 3/2*b*L
          nlinarith only [hlu,hminus])
    simpa only [card_singleton,Nat.cast_one,one_mul,sum_singleton,one_pow] using hm
  · have hp := poisson_atom_upper (a*L) (by positivity) hk
    have hm := poisson_atom_upper (b*L) (by positivity) hl
    have hpair := mul_le_mul hp hm (by positivity) (by positivity)
    have hkp : a*(L : ℝ)/2 ≤ k := by nlinarith only [hkhi,hplus]
    have hlp : b*(L : ℝ)/2 ≤ l := by linarith only [hll,show 0 ≤ b*(L : ℝ) by positivity]
    have hden : Real.sqrt (a*b)*(L : ℝ)/2 ≤ Real.sqrt k*Real.sqrt l := by
      have hh := mul_le_mul (Real.sqrt_le_sqrt hkp) (Real.sqrt_le_sqrt hlp) (by positivity) (by positivity)
      have he : Real.sqrt (a*(L : ℝ)/2) * Real.sqrt (b*(L : ℝ)/2) =
          Real.sqrt (a*b)*(L : ℝ)/2 := by
        rw [← Real.sqrt_mul (by positivity),
          show (a*(L : ℝ)/2)*(b*(L : ℝ)/2) = (a*b)*((L : ℝ)/2)^2 by ring,
          Real.sqrt_mul (by positivity),Real.sqrt_sq (by positivity)]
        ring
      rwa [he] at hh
    have hd : 0 < Real.sqrt k*Real.sqrt l := by positivity
    have hu := div_le_div₀ (by norm_num : (0 : ℝ) ≤ 1) le_rfl (by positivity : 0 < Real.sqrt (a*b)*(L : ℝ)/2) hden
    simp only [← mul_div_mul_comm,one_mul] at hpair
    have hnorm : 1/(Real.sqrt (a*b)*(L : ℝ)/2) = 2/(Real.sqrt (a*b)*L) := by ring
    rw [hnorm] at hu
    have hh := hpair.trans hu
    unfold rowReference; simp only [SequentialDecisionRisk.FiniteSupportSelectionBayes.b,if_pos hi]
    have hae : (L : ℝ)*(1+r)/2 = a*L := by dsimp [a]; ring
    have hbe : (L : ℝ)*(1-r)/2 = b*L := by dsimp [b]; ring
    try simp only [Prod.fst,Prod.snd]
    rw [hae,hbe]
    simpa only [a,b,k,l,← mul_div_mul_comm] using hh
end
end D5.S3.Estimation.TimeArrow.NativeRectangleReferenceMass
namespace D5.S3.Estimation.TimeArrow.NativeCalibrationRootBudgets
noncomputable section
private theorem all_row_root_from_residual {M : ℕ} (a : Fin M → ℝ)
    (q x v b : ℝ) (hM : 0 < M) (hv : 0 < v)
    (hroot : (∑ i, Real.sigmoid (x + a i)) = q)
    (hres : |(∑ i, Real.sigmoid (a i)) - q| ≤ b)
    (hvar : v ≤ ∑ i, Real.sigmoid (a i) * (1 - Real.sigmoid (a i)))
    (hsmall : b ≤ v / 2 * Real.log 2) :
    |x| ≤ Real.log 2 ∧ |x| ≤ 2 * b / v ∧
      v / 2 ≤ ∑ i, Real.sigmoid (x + a i) * (1 - Real.sigmoid (x + a i)) ∧
      (∑ i, Real.sigmoid (x + a i) * (1 - Real.sigmoid (x + a i))) ≤ q := by
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  let F := fun u : ℝ => ∑ i, Real.sigmoid (u + a i)
  let V := fun u : ℝ => ∑ i, Real.sigmoid (u + a i) * (1 - Real.sigmoid (u + a i))
  let d := Real.log (2 : ℝ)
  have hd : 0 < d := Real.log_pos (by norm_num)
  have hder (u : ℝ) : HasDerivAt F (V u) u := by
    have hh := HasDerivAt.sum (fun i (_ : i ∈ (univ : Finset (Fin M))) =>
      D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_shift_deriv (a i) u)
    have he : (∑ i : Fin M, fun z : ℝ => Real.sigmoid (z + a i)) = F := by
      ext z
      simp only [Finset.sum_apply, F]
    rw [he] at hh; exact hh
  have hV (u : ℝ) : 0 < V u := by
    exact sum_pos (fun i _ => mul_pos (Real.sigmoid_pos _) (sub_pos.mpr (Real.sigmoid_lt_one _))) univ_nonempty
  have hmono : StrictMono F := strictMono_of_deriv_pos fun u => by
    rw [(hder u).deriv]; exact hV u
  have htilt (u : ℝ) (hu : |u| ≤ d) :
      1 / 2 ≤ Real.exp (-u) ∧ Real.exp (-u) ≤ 2 := by
    have hh := abs_le.mp hu
    constructor
    · calc
        1 / 2 = Real.exp (-d) := by simp [d, Real.exp_neg, Real.exp_log]
        _ ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith only [hh.2])
    · calc Real.exp (-u) ≤ Real.exp d := Real.exp_le_exp.mpr (by linarith only [hh.1]) _ = 2 := Real.exp_log (by norm_num)
  have hlower (u : ℝ) (hu : |u| ≤ d) : v / 2 ≤ V u := by
    have ht := htilt u hu
    have hh := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin M))) =>
      (D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds.sigmoid_variance_tilt
        (a i) u ht.1 ht.2).1)
    rw [← sum_div] at hh; simp only [add_comm] at hh
    have hb := mul_le_mul_of_nonneg_left hvar (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    dsimp [V]; linarith only [hh, hb]
  have hb := D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds.root_box_of_residual
    F q 0 x d (v / 2) b hd (by positivity) hmono
    (fun u _ => (hder u).continuousAt.continuousWithinAt)
    (fun u _ => (hder u).differentiableAt.differentiableWithinAt)
    (fun u hu => by
      rw [(hder u).deriv]
      have hh := interior_subset hu
      exact hlower u (abs_le.mpr (by constructor <;> linarith only [hh.1, hh.2])))
    hroot (by simpa only [F, zero_add] using hres) hsmall
  simp only [sub_zero] at hb
  refine ⟨hb.1, ?_, hlower x hb.1, ?_⟩
  · apply (le_div_iff₀ hv).mpr
    nlinarith only [hb.2]
  · rw [← hroot]
    exact sum_le_sum fun i _ => mul_le_of_le_one_right (Real.sigmoid_nonneg _) (by linarith only [Real.sigmoid_nonneg (x + a i)])
/-- The original pair and path laws share a probability budget for the full
calibration root and its variance. The reference lower variance is evaluated
at the complete fixed count-level calibration. -/
theorem native_calibration_root_budget (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        6 ≤ M → (L : ℝ) / M ≤ 1 / 45 →
        ∀ (S : Support M q) (e : Experiment) (i j : Fin M),
          i ∈ S.val → j ∉ S.val → ∀ v b : ℝ, 0 < v → 0 < b →
          let p := referenceParameter M q r
          let V := ∑ k : Fin M, ∑' c, (p c * (1 - p c)) * rowReference S r L k c
          v ≤ V → b ≤ v / 4 * Real.log 2 →
          ∀ x : Obs M (2 * M * L) e → ℝ,
          (∀ o, (∑ k : Fin M, Real.sigmoid (x o + score q r e o k -
            Real.log (((M - q : ℕ) : ℝ) / q))) = q) →
          let D := fun o => ∑ k : Fin M, Real.sigmoid (x o + score q r e o k - Real.log (((M - q : ℕ) : ℝ) / q)) *
              (1 - Real.sigmoid (x o + score q r e o k - Real.log (((M - q : ℕ) : ℝ) / q)))
          let B := 3 * (q : ℝ) + 8 * (A * (L : ℝ) ^ 3 / M) * (q : ℝ) ^ 2 +
            10 * (M : ℝ) ^ 2 * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ)))
          (∑ o, if 4 * b / v < |x o| ∨ D o < v / 4 ∨ q < D o
            then probability r e S o else 0) ≤ B / b ^ 2 + B / (v / 2) ^ 2 := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ := native_reference_calibration_deviation κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e i j hi hj v b hv hb
  dsimp only
  intro hV hbudget x hx
  let p := referenceParameter M q r
  let V := ∑ k : Fin M, ∑' c, (p c * (1 - p c)) * rowReference S r L k c
  let P := fun o : Obs M (2 * M * L) e =>
    ∑ k : Fin M, p (count e o k 1, count e o k (-1))
  let D0 := fun o : Obs M (2 * M * L) e =>
    ∑ k : Fin M, p (count e o k 1, count e o k (-1)) *
      (1 - p (count e o k 1, count e o k (-1)))
  have hdev := (h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e i j hi hj b (v / 2) hb (by positivity)).2.2
  apply le_trans _ hdev
  apply sum_le_sum
  intro o _
  have hr1 : r < 1 := by linarith only [hrκ, hκ]
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hc1 : compensation M q r < 1 := by linarith only [hcκ, hκ]
  have hp := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hc hc1 e).2.1.1 S o
  by_cases hbad : b < |P o - q| ∨ v / 2 < |D0 o - V|
  · simp only [hbad, if_true] split_ifs <;> linarith only [hp]
  · have hgood := not_or.mp hbad
    have hmean : |P o - q| ≤ b := le_of_not_gt hgood.1
    have hvar : v / 2 ≤ D0 o := by
      have hh := abs_le.mp (le_of_not_gt hgood.2)
      linarith only [hh.1, hV]
    have hh := all_row_root_from_residual (fun k => score q r e o k - Real.log (((M - q : ℕ) : ℝ) / q))
      q (x o) (v / 2) b (by omega) (by positivity)
      (by simpa only [add_sub_assoc] using hx o)
      (by simpa only [P, p, referenceParameter, score] using hmean)
      (by simpa only [D0, p, referenceParameter, score] using hvar)
      (by linarith only [hbudget])
    have hroot : |x o| ≤ 4 * b / v := by convert hh.2.1 using 1 <;> field_simp <;> ring
    have hvarroot := hh.2.2
    simp only [hbad, if_false]
    split_ifs with hfail
    · rcases hfail with hfail | hfail | hfail
      · exact False.elim (not_lt_of_ge hroot hfail)
      · exact False.elim (not_lt_of_ge (by simpa only [add_sub_assoc, div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hvarroot.1) hfail)
      · exact False.elim (not_lt_of_ge (by simpa only [add_sub_assoc] using hvarroot.2) hfail)
    · exact le_rfl
/-- The explicit signal count window supplies the variance input to the
native complete-root probability budget. -/
theorem native_calibration_window_root_budget (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        4 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        6 ≤ M → (L : ℝ) / M ≤ 1 / 45 →
        4 * Real.sqrt L ≤ ((1 + r) / 2) * L →
        4 * Real.sqrt L ≤ ((1 - r) / 2) * L →
        ((((1 + r) / 2) * L) * Real.log ((1 + r) / (1 - compensation M q r)) +
          (((1 - r) / 2) * L) * Real.log ((1 - r) / (1 + compensation M q r)) -
            Real.log (((M - q : ℕ) : ℝ) / q) ≤
          Real.sqrt L * (Real.log ((1 + r) / (1 - compensation M q r)) -
            Real.log ((1 - r) / (1 + compensation M q r)))) →
        ∀ (S : Support M q) (e : Experiment) (i j : Fin M),
          i ∈ S.val → j ∉ S.val →
          let v := (q : ℝ) / 8 * (Real.exp (-(2 : ℝ) ^ 2 / ((1 + r) / 2) - 1) * Real.exp (-(2 : ℝ) ^ 2 / ((1 - r) / 2) - 1) /
              (Real.sqrt ((3 / 2) * ((1 + r) / 2)) *
                Real.sqrt ((3 / 2) * ((1 - r) / 2))))
          ∀ b : ℝ, 0 < b → b ≤ v / 4 * Real.log 2 →
          ∀ x : Obs M (2 * M * L) e → ℝ,
          (∀ o, (∑ k : Fin M, Real.sigmoid (x o + score q r e o k -
            Real.log (((M - q : ℕ) : ℝ) / q))) = q) →
          let D := fun o => ∑ k : Fin M, Real.sigmoid (x o + score q r e o k - Real.log (((M - q : ℕ) : ℝ) / q)) *
              (1 - Real.sigmoid (x o + score q r e o k - Real.log (((M - q : ℕ) : ℝ) / q)))
          let B := 3 * (q : ℝ) + 8 * (A * (L : ℝ) ^ 3 / M) * (q : ℝ) ^ 2 +
            10 * (M : ℝ) ^ 2 * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ)))
          (∑ o, if (4 * b / v < |x o| ∨ D o < v / 4 ∨ q < D o) ∨
              ¬∀ k : Fin M, count e o k 1 + count e o k (-1) ≤ 8 * L
            then probability r e S o else 0) ≤ B / b ^ 2 + B / (v / 2) ^ 2 +
              (M : ℝ) * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ := native_calibration_root_budget κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM hplus hminus hcenter
  intro S e i j hi hj
  dsimp only
  intro b hb hbudget x hx
  have hr1 : r < 1 := by linarith only [hrκ, hκ]
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have ha : 0 < (3 / 2) * ((1 + r) / 2) := by linarith only [hr]
  have hc : 0 < (3 / 2) * ((1 - r) / 2) := by linarith only [hr1]
  have hv : 0 < (q : ℝ) / 8 * (Real.exp (-(2 : ℝ) ^ 2 / ((1 + r) / 2) - 1) * Real.exp (-(2 : ℝ) ^ 2 / ((1 - r) / 2) - 1) /
        (Real.sqrt ((3 / 2) * ((1 + r) / 2)) *
          Real.sqrt ((3 / 2) * ((1 - r) / 2)))) := by positivity
  have hroot := h M q L r hMM hq hqm hr hrκ hcκ (by omega) hLη hsmall hM6 hLM S e i j hi hj _ b hv hb
    (reference_linear_variance_lower S r κ hκ hr hrκ hcκ hL hq hqm i j hi hj
      hplus hminus hcenter) hbudget x hx
  have he : 0 ≤ compensation M q r := by unfold compensation; positivity
  have he1 : compensation M q r < 1 := by linarith only [hcκ, hκ]
  have hcut := D5.S3.Estimation.TimeArrow.NativeRowCountTail.native_all_row_count_cut r S hq hqm hr hr1 he1 hM6 (by omega) hLM e
  have law := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 he he1 e).2.1
  let K := fun o : Obs M (2 * M * L) e =>
    ∀ k : Fin M, count e o k 1 + count e o k (-1) ≤ 8 * L
  have hpartition : (∑ o, if K o then probability r e S o else 0) +
      (∑ o, if ¬K o then probability r e S o else 0) = 1 := by
    rw [← sum_filter, ← sum_filter, sum_filter_add_sum_filter_not]; exact law.2 S
  have hcutbad : (∑ o, if ¬K o then probability r e S o else 0) ≤
      (M : ℝ) * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) := by
    change 1 - (M : ℝ) * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) ≤ ∑ o, if K o then probability r e S o else 0 at hcut
    linarith only [hpartition, hcut]
  apply le_trans _ (add_le_add hroot hcutbad)
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro o _
  have hp := law.1 S o
  by_cases hk : K o
  · dsimp only [K] at hk
    simp only [K, hk, forall_true_iff, not_true_eq_false, if_false, or_false, add_zero, le_refl]
  · dsimp only [K] at hk
    simp only [K, hk, not_false_eq_true, if_true, or_true]
    split_ifs <;> linarith only [hp]
end
end D5.S3.Estimation.TimeArrow.NativeCalibrationRootBudgets
open D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds
open D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback
noncomputable section
set_option maxHeartbeats 800000 in
/-- Constants depend on the original amplitude alone. A single complete
anchor supplies the root and variance budgets for every central histogram;
the compensated derivative is then bounded by positive multiples of N/q. -/
theorem anchored_central_shared_calibration (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ d η : ℝ, 0 < d ∧ 0 < η ∧
    ∀ (ι : Type*) [Fintype ι] (outside : ι → ℝ),
    ∀ (ε N R U q bg ρ γ a v B tStar xStar : ℝ),
      0 < N → 0 < q → q < (Fintype.card ι : ℝ) + N →
      0 < ρ → 0 ≤ γ → γ ≤ ρ^2/2 → 0 < v → 0 ≤ bg → bg ≤ B*N →
      ρ*N ≤ R → R ≤ (1-ρ)*N → ρ*N ≤ U → U ≤ (1-ρ)*N →
      calibratedMean outside r ε N R U tStar xStar = q →
      v*q ≤ calibratedVariance outside r ε N R U tStar xStar →
      |tStar-U*R/N| ≤ 2*Real.sqrt N →
      γ*N+2*Real.sqrt N ≤ v*q/2 →
      2*(γ*N+2*Real.sqrt N) ≤ v*q/4*Real.log 2 →
      |xStar|+8*(γ*N+2*Real.sqrt N)/(v*q) ≤ a*N/q →
      a ≤ ρ^2*d/8 → a*N/q < η → |ε| < η →
      ∃ θ : ℝ → ℝ, ∀ t : ℝ, |t-U*R/N| ≤ γ*N →
        calibratedMean outside r ε N R U t (θ t) = q ∧
        |θ t| ≤ a*N/q ∧
        |θ t-xStar| ≤ 8*(γ*N+2*Real.sqrt N)/(v*q) ∧
        v*q/4 ≤ calibratedVariance outside r ε N R U t (θ t) ∧
        calibratedVariance outside r ε N R U t (θ t) ≤ q ∧
        HasDerivAt θ (-checkerboard r ε (θ t) /
          calibratedVariance outside r ε N R U t (θ t)) t ∧
        (∀ᶠ u in 𝓝 t, calibratedMean outside r ε N R U u (θ u) = q) ∧
        ∃ z : ℝ, (ρ^2*d/32)*(N/q) ≤ z ∧
          z ≤ (a/4+2*(B+1)/v)*(N/q) ∧
          HasDerivAt (fun u => (bg+u)*Real.sigmoid (θ u)-u/2) z t := by
  obtain ⟨d,η,hd,hη,hη2,hnegative⟩ := compensated_feedback_box hr hr1
  refine ⟨d,η,hd,hη,?_⟩
  intro ι _ outside ε N R U q bg ρ γ a v B tStar xStar hN hq hqM hρ hγ hγρ hv hbg hbgB hR hR' hU hU' hanchor hV
    hstar hw hsmall hprecision ha hηscale hε
  let w := γ*N+2*Real.sqrt N
  have hw0 : 0 ≤ w := by dsimp [w]; positivity
  have hcentral : γ*N ≤ ρ^2*N/2 := by nlinarith only [hγρ,hN]
  obtain ⟨θ,hθ⟩ := balanced_shared_curve outside r ε N R U q ρ (γ*N) hN hq hqM hρ hcentral hR hR' hU hU'
  refine ⟨θ,fun t ht => ?_⟩
  have hc0 := central_four_cells_lower N R U ρ t (γ*N) hN hρ.le hR hR' hU hU' ht
  have hc (j : Fin 4) : 0 ≤ cellCounts N R U t j := by
    have hh := hc0 j
    nlinarith only [hh,hcentral,sq_nonneg ρ,hN]
  have hdist : |t-tStar| ≤ w := by
    calc
      |t-tStar| = |(t-U*R/N)+(U*R/N-tStar)| := by congr 1; ring
      _ ≤ |t-U*R/N|+|U*R/N-tStar| := abs_add_le _ _
      _ ≤ w := by rw [abs_sub_comm (U*R/N) tStar]; exact add_le_add ht hstar
  have hgap : 0 < calibratedVariance outside r ε N R U tStar xStar-w := by
    have hvq := mul_pos hv hq
    dsimp only [w] at *; linarith only [hw,hV,hvq]
  have hbudget : 2*w ≤
      (calibratedVariance outside r ε N R U tStar xStar-w)/2*Real.log 2 := by
    have hlog := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have hh : v*q/4 ≤ (calibratedVariance outside r ε N R U tStar xStar-w)/2 := by linarith only [hw,hV]
    exact hsmall.trans (mul_le_mul_of_nonneg_right hh hlog)
  have he := hθ t ht
  have hb := shared_root_central_bootstrap outside r ε N R U q t tStar xStar (θ t) w
    hN hc hdist hanchor he.1 (by linarith only [hgap]) hbudget
  have hmove : |θ t-xStar| ≤ 8*w/(v*q) := by
    have hden : v*q/2 ≤ calibratedVariance outside r ε N R U tStar xStar-w := by linarith only [hw,hV]
    calc
      _ ≤ 4*w/(calibratedVariance outside r ε N R U tStar xStar-w) := hb.2.1
      _ ≤ 4*w/(v*q/2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 8*w/(v*q) := by ring
  have hx : |θ t| ≤ a*N/q := by
    calc
      |θ t| = |xStar+(θ t-xStar)| := by congr 1; ring
      _ ≤ |xStar|+|θ t-xStar| := abs_add_le _ _
      _ ≤ a*N/q := by linarith only [hmove,hprecision]
  have hlow : v*q/4 ≤ calibratedVariance outside r ε N R U t (θ t) := by linarith only [hb.2.2.1,hw,hV]
  have hhigh : calibratedVariance outside r ε N R U t (θ t) ≤ q := by
    rw [← he.1]
    unfold calibratedVariance calibratedMean
    apply add_le_add
    · apply sum_le_sum
      intro i _
      exact mul_le_of_le_one_right (Real.sigmoid_nonneg _) (by linarith only [Real.sigmoid_nonneg (θ t+outside i)])
    · apply sum_le_sum
      intro j _
      exact mul_le_of_le_one_right (mul_nonneg (hc j) (Real.sigmoid_nonneg _))
        (by linarith only [Real.sigmoid_nonneg (θ t+offsets r ε j)])
  have hB0 : 0 ≤ bg+t := by
    have hh := hc 0
    change 0 ≤ t at hh; linarith only [hbg,hh]
  have htlo : ρ^2*N/2 ≤ t := by
    have hh := hc0 0
    change ρ^2*N-γ*N ≤ t at hh; linarith only [hh,hcentral]
  have hthi : t ≤ N := by
    have hh := hc 1
    change 0 ≤ U-t at hh; nlinarith only [hh,hU',hρ,hN]
  have hBlo : ρ^2*N/2 ≤ bg+t := by linarith only [htlo,hbg]
  have hBhi : bg+t ≤ (B+1)*N := by nlinarith only [hbgB,hthi]
  have hfeedback := compensated_feedback_bounds r ε (θ t) (bg+t)
    (calibratedVariance outside r ε N R U t (θ t)) d (v*q/4) q (a*N/q)
    (by positivity) hlow hhigh hB0 hd.le
    (hnegative ε (θ t) hε (hx.trans_lt hηscale)) hx
    (hx.trans (hηscale.le.trans hη2))
  let z := Real.sigmoid (θ t)-1/2-(bg+t)*Real.sigmoid (θ t)* (1-Real.sigmoid (θ t))*checkerboard r ε (θ t)/
      calibratedVariance outside r ε N R U t (θ t)
  have hzlo : (ρ^2*d/32)*(N/q) ≤ z := by
    have hh : ρ^2*N/2*d/(8*q) ≤ (bg+t)*d/(8*q) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBlo hd.le) (by positivity)
    have hh' : a*N/q/4 ≤ (ρ^2*d/8)*N/q/4 := by
      exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ha hN.le) hq.le) (by norm_num)
    calc
      _ = ρ^2*N/2*d/(8*q)-(ρ^2*d/8)*N/q/4 := by field_simp; ring
      _ ≤ (bg+t)*d/(8*q)-a*N/q/4 := sub_le_sub hh hh'
      _ ≤ z := hfeedback.1
  have hzhi : z ≤ (a/4+2*(B+1)/v)*(N/q) := by
    have hh : (bg+t)/(2*(v*q/4)) ≤ ((B+1)*N)/(2*(v*q/4)) := div_le_div_of_nonneg_right hBhi (by positivity)
    have heq : a*N/q/4+((B+1)*N)/(2*(v*q/4)) =
        (a/4+2*(B+1)/v)*(N/q) := by field_simp; ring
    dsimp only [z]; linarith only [hfeedback.2,hh,heq]
  refine ⟨he.1,hx,hmove,hlow,hhigh,he.2.1,he.2.2.1,z,hzlo,hzhi,?_⟩
  exact compensated_group_deriv outside r ε N R U q bg t (θ t) _ θ he.2.1 rfl he.2.2.1 (ne_of_gt he.2.2.2)
end
end D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback
