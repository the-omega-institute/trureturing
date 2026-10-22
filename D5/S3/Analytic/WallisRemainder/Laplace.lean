/- GID: D5/S3/Analytic/WallisRemainder/Laplace
   generality: G
   mirror-B: D5/B/S3/Analytic/WallisRemainder/Laplace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics, mathlib/module/Mathlib.Analysis.SpecialFunctions.Integrals.Basic, mathlib/module/Mathlib.Analysis.SpecialFunctions.FrullaniIntegral, mathlib/module/Mathlib.Analysis.SpecialFunctions.ImproperIntegrals]
   utility: none
   digest: The logarithmic Wallis remainder has a positive convergent hyperbolic Laplace representation. -/

import D5.S3.Analytic.WallisRemainder.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import D5.S3.Observer.Fluctuation.ThermalCoefficientFloor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Set Filter MeasureTheory
open scoped Topology
open D5.S3.Analytic.WallisRemainder.Defs
namespace D5.S3.Analytic.WallisRemainder.Laplace

noncomputable def r (x : ℝ) : ℝ := -Real.log (wallisB x)

private lemma log_wallisB {x : ℝ} (hx : 0 < x) :
    Real.log (wallisB x) = Real.log x / 2 + Real.log (Real.Gamma (x + 1/2)) -
      Real.log (Real.Gamma (x + 1)) := by
  rw [wallisB, Real.log_div
    (mul_ne_zero (Real.sqrt_pos.2 hx).ne' (Real.Gamma_pos_of_pos (by linarith)).ne')
    (Real.Gamma_pos_of_pos (by linarith)).ne',
    Real.log_mul (Real.sqrt_pos.2 hx).ne' (Real.Gamma_pos_of_pos (by linarith)).ne',
    Real.log_sqrt hx.le]

private lemma log_Gamma_step {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma (x + 1)) = Real.log x + Real.log (Real.Gamma x) := by
  rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']

/-- The negative logarithm is the midpoint convexity gap of log Gamma. -/
private theorem r_eq_midpoint_gap {x : ℝ} (hx : 0 < x) :
    r x = (Real.log (Real.Gamma x) + Real.log (Real.Gamma (x + 1))) / 2 -
      Real.log (Real.Gamma (x + 1/2)) := by
  rw [r, log_wallisB hx, log_Gamma_step hx]
  ring

/-- The half-step equation follows from the Gamma recurrence. -/
private theorem r_add_half {x : ℝ} (hx : 0 < x) :
    r x + r (x + 1/2) = Real.log ((x + 1/2) / x) / 2 := by
  have hhalf : 0 < x + 1/2 := by linarith
  rw [r, r, log_wallisB hx, log_wallisB hhalf,
    show x + 1 / 2 + 1 / 2 = x + 1 by ring,
    log_Gamma_step hhalf, log_Gamma_step hx,
    Real.log_div hhalf.ne' hx.ne']
  ring

/-- Nonnegativity and a vanishing elementary upper bound. -/
private theorem r_bounds {x : ℝ} (hx : 0 < x) :
    0 ≤ r x ∧ r x ≤ Real.log ((x + 1/2) / x) / 2 := by
  have hn : ∀ {y : ℝ}, 0 < y → 0 ≤ r y := by
    intro y hy
    rw [r_eq_midpoint_gap hy]
    have h := Real.convexOn_log_Gamma.2 hy (show y + 1 ∈ Ioi 0 by change 0 < y + 1; linarith)
      (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
      (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    simp only [Function.comp_apply, smul_eq_mul] at h
    have he : 1/2 * y + 1/2 * (y + 1) = y + 1/2 := by ring
    rw [he] at h
    linarith
  exact ⟨hn hx, by linarith [r_add_half hx, hn (show 0 < x + 1/2 by linarith)]⟩

/-- The logarithmic remainder tends to zero at positive infinity. -/
private theorem tendsto_r_atTop : Tendsto r atTop (𝓝 0) := by
  have hi : Tendsto (fun x : ℝ => (1/2 : ℝ) / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hl : Tendsto (fun x : ℝ => Real.log (1 + (1/2 : ℝ) / x) / 2)
      atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds.add hi).log (by norm_num : (1 : ℝ) + 0 ≠ 0)).div_const 2
    simpa using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hl
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (r_bounds hx).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have he : (x + 1/2) / x = 1 + (1/2 : ℝ) / x := by field_simp
    rw [← he]
    exact (r_bounds hx).2

/-- The Laplace kernel for the logarithmic remainder. -/
noncomputable def laplaceKernel (x t : ℝ) : ℝ :=
  Real.exp (-x * t) * Real.tanh (t / 4) / (2 * t)

/-- The proposed Laplace integral, over the positive ray. -/
noncomputable def laplace (x : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), laplaceKernel x t

private lemma tanh_quarter_bounds {t : ℝ} (ht : 0 < t) :
    0 < Real.tanh (t / 4) ∧ Real.tanh (t / 4) ≤ t / 4 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  constructor
  · exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  · exact (div_le_iff₀ (Real.cosh_pos _)).mpr
      (D5.S3.Observer.Fluctuation.ThermalCoefficientFloor.sinh_le_self_mul_cosh_of_nonneg
        (by linarith))

lemma laplaceKernel_bounds {x t : ℝ} (ht : 0 < t) :
    0 < laplaceKernel x t ∧ laplaceKernel x t ≤ Real.exp (-x * t) / 8 := by
  obtain ⟨hp, hb⟩ := tanh_quarter_bounds ht
  constructor
  · exact div_pos (mul_pos (Real.exp_pos _) hp) (by linarith)
  · unfold laplaceKernel
    apply (div_le_iff₀ (show 0 < 2 * t by linarith)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hb (Real.exp_pos (-x * t)).le]

/-- Absolute convergence of the positive-ray Laplace integral. -/
theorem integrableOn_laplaceKernel {x : ℝ} (hx : 0 < x) :
    IntegrableOn (laplaceKernel x) (Ioi 0) := by
  apply ((integrableOn_exp_mul_Ioi (show -x < 0 by linarith) 0).div_const 8).mono'
  · unfold laplaceKernel
    exact ((Real.measurable_exp.comp (by fun_prop)).mul
      (by simp_rw [Real.tanh_eq_sinh_div_cosh]; fun_prop)).div
      (by fun_prop) |>.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (laplaceKernel_bounds ht).1]
    exact (laplaceKernel_bounds ht).2

private lemma tanh_halfstep (t : ℝ) :
    (1 + Real.exp (-t / 2)) * Real.tanh (t / 4) = 1 - Real.exp (-t / 2) := by
  have he : Real.exp (-t / 2) = Real.exp (-(t / 4)) / Real.exp (t / 4) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [he, Real.tanh_eq]
  field_simp (disch := first | assumption | positivity)

/-- The Laplace integral satisfies the same half-step equation. -/
private theorem laplace_add_half {x : ℝ} (hx : 0 < x) :
    laplace x + laplace (x + 1/2) = Real.log ((x + 1/2) / x) / 2 := by
  have hhalf : 0 < x + 1/2 := by linarith
  have hkernel (t : ℝ) :
      laplaceKernel x t + laplaceKernel (x + 1/2) t =
        (Real.exp (-x * t) - Real.exp (-(x + 1/2) * t)) / t / 2 := by
    have he : Real.exp (-(x + 1/2) * t) = Real.exp (-x * t) * Real.exp (-t / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [laplaceKernel, laplaceKernel, he]
    have h := tanh_halfstep t
    convert congrArg (fun a : ℝ => Real.exp (-x * t) * a / (2 * t)) h using 1 <;> ring
  have hi : IntegrableOn (fun t : ℝ => t⁻¹ •
      (Real.exp (-(x*t)) - Real.exp (-((x+1/2)*t)))) (Ioi 0) := by
    apply (((integrableOn_laplaceKernel hx).add
      (integrableOn_laplaceKernel hhalf)).const_mul 2).congr
    filter_upwards [] with t
    change 2 * (laplaceKernel x t + laplaceKernel (x+1/2) t) = _
    rw [hkernel]
    simp only [smul_eq_mul, neg_mul]
    ring
  have hf : LocallyIntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) :=
    (Real.continuous_exp.comp continuous_neg).continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hzero : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    have h : ContinuousAt (fun t : ℝ => Real.exp (-t)) 0 := by fun_prop
    simpa only [neg_zero, Real.exp_zero] using h.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have heval := Frullani.integral_Ioi_eq hf hx hhalf hzero
    Real.tendsto_exp_neg_atTop_nhds_zero hi
  rw [laplace, laplace, ← integral_add (integrableOn_laplaceKernel hx)
    (integrableOn_laplaceKernel hhalf)]
  calc
    (∫ t in Ioi (0 : ℝ), laplaceKernel x t + laplaceKernel (x + 1/2) t) =
        (∫ t in Ioi (0 : ℝ), t⁻¹ •
          (Real.exp (-(x*t)) - Real.exp (-((x+1/2)*t)))) / 2 := by
      rw [← integral_div]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hkernel]
      simp only [smul_eq_mul, neg_mul]
      ring
    _ = Real.log ((x + 1/2) / x) / 2 := by
      rw [heval]
      simp

/-- The Laplace integral is positive and bounded by the elementary exponential integral. -/
theorem laplace_bounds {x : ℝ} (hx : 0 < x) :
    0 < laplace x ∧ laplace x ≤ 1 / (8 * x) := by
  have hnonneg : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ laplaceKernel x t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact (laplaceKernel_bounds ht).1.le
  constructor
  · rw [laplace, setIntegral_pos_iff_support_of_nonneg_ae hnonneg (integrableOn_laplaceKernel hx)]
    have hs : Function.support (laplaceKernel x) ∩ Ioi 0 = Ioi 0 := by
      ext t
      constructor
      · exact And.right
      · intro ht
        exact ⟨(laplaceKernel_bounds ht).1.ne', ht⟩
    rw [hs]
    simp
  · have hb := integral_mono_ae (integrableOn_laplaceKernel hx)
      ((integrableOn_exp_mul_Ioi (show -x < 0 by linarith) 0).div_const 8) (by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact (laplaceKernel_bounds ht).2)
    rw [integral_div, integral_exp_mul_Ioi (show -x < 0 by linarith) 0] at hb
    simp only [mul_zero, Real.exp_zero, neg_div_neg_eq] at hb
    change (∫ t in Ioi (0 : ℝ), laplaceKernel x t) ≤ _
    convert hb using 1; ring

/-- Decay of the Laplace integral at positive infinity. -/
private theorem tendsto_laplace_atTop : Tendsto laplace atTop (𝓝 0) := by
  have hi : Tendsto (fun x : ℝ => 1 / (8 * x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hi
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (laplace_bounds hx).1.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (laplace_bounds hx).2

/-- Equality of the logarithmic remainder and its Laplace representation. -/
theorem r_eq_laplace {x : ℝ} (hx : 0 < x) :
    -Real.log (wallisB x) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * Real.tanh (t / 4) / (2 * t) := by
  let d : ℝ → ℝ := fun y => r y - laplace y
  have hstep {y : ℝ} (hy : 0 < y) : d (y + 1/2) = -d y := by
    dsimp [d]
    linarith [r_add_half hy, laplace_add_half hy]
  have hperiod {y : ℝ} (hy : 0 < y) : d (y + 1) = d y := by
    have h1 := hstep hy
    have h2 := hstep (show 0 < y + 1/2 by linarith)
    rw [show y + 1/2 + 1/2 = y + 1 by ring] at h2
    linarith
  have hnat (n : ℕ) : d (x + n) = d x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, ← add_assoc, hperiod (by positivity), ih]
  have hlim : Tendsto (fun n : ℕ => d (x + n)) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => x + (n : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop
    simpa only [d, Function.comp_def, sub_self] using
      (tendsto_r_atTop.sub tendsto_laplace_atTop).comp ht
  simp_rw [hnat] at hlim
  have hd : d x = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  exact sub_eq_zero.mp hd

end D5.S3.Analytic.WallisRemainder.Laplace
