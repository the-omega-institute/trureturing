/- GID: D5/S3/Weil/ZetaRvm/HorizontalLogTail
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaRvm/HorizontalLogTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual principal-log zeta tail decay, truncation and oriented height transport. -/

import D5.S3.Weil.Mertens.Cryptids.VonMangoldtCount.Integral
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The principal-log zeta tail in the right half-plane

The shifted Dirichlet series gives a uniform exponential bound with
`q = π²/6 - 1` and `C = q/(1-q)`. Integrating this bound controls the
actual improper tail. Cauchy's rectangle identity and the same bound
remove the right edge and give transport for every pair of real heights.
This controls the right boundary in Littlewood identities. The central
Riemann-hypothesis sign inequality `E ≤ 0` remains unproved.
-/
noncomputable section

open Complex Set Filter MeasureTheory
open scoped Topology Interval

namespace Zeta23.RvM

local notation "q" => (Real.pi ^ 2 / 6 - 1 : ℝ)
local notation "Ctail" => (q / (1 - q))

private lemma norm_shifted_cpow_decay {s : ℂ} (hs : 2 ≤ s.re) (n : ℕ) :
    ‖1 / (n + 2 : ℂ) ^ s‖ ≤
      (1 / (n + 2 : ℝ) ^ 2) * (2 : ℝ) ^ (2 - s.re) := by
  have hn : (0 : ℝ) < n + 2 := by positivity
  have hn2 : (2 : ℝ) ≤ n + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hc : (n + 2 : ℂ) = ((n + 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [norm_div, norm_one, hc, Complex.norm_cpow_eq_rpow_re_of_pos hn]
  calc
    1 / (n + 2 : ℝ) ^ s.re = (n + 2 : ℝ) ^ (-s.re) := by
      rw [Real.rpow_neg hn.le, one_div]
    _ = (n + 2 : ℝ) ^ (-2 : ℝ) * (n + 2 : ℝ) ^ (2 - s.re) := by
      rw [← Real.rpow_add hn]
      congr 1; ring
    _ ≤ (n + 2 : ℝ) ^ (-2 : ℝ) * (2 : ℝ) ^ (2 - s.re) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by norm_num) hn2 (by linarith))
        (Real.rpow_nonneg hn.le _)
    _ = (1 / (n + 2 : ℝ) ^ 2) * (2 : ℝ) ^ (2 - s.re) := by
      rw [Real.rpow_neg hn.le, Real.rpow_two, one_div]

private lemma norm_zeta_sub_one_decay {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ q * (2 : ℝ) ^ (2 - s.re) := by
  let f : ℕ → ℂ := fun n ↦ 1 / (n + 2 : ℂ) ^ s
  have hsq :=
    ConjectureMachines.Semantics.Riemann.VonMangoldtCount.hasSum_one_div_nat_add_two_sq
  have hnorm : Summable (fun n ↦ ‖f n‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (ConjectureMachines.Semantics.Riemann.VonMangoldtCount.norm_one_div_nat_add_two_cpow_le hs)
      hsq.summable
  have hscaled : HasSum
      (fun n : ℕ ↦ (1 / (n + 2 : ℝ) ^ 2) * (2 : ℝ) ^ (2 - s.re))
      (q * (2 : ℝ) ^ (2 - s.re)) := hsq.mul_right _
  rw [ConjectureMachines.Semantics.Riemann.VonMangoldtCount.riemannZeta_sub_one_eq_tsum
    (by linarith : 1 < s.re)]
  calc
    ‖∑' n : ℕ, f n‖ ≤ ∑' n : ℕ, ‖f n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, (1 / (n + 2 : ℝ) ^ 2) * (2 : ℝ) ^ (2 - s.re) :=
      hnorm.tsum_le_tsum (norm_shifted_cpow_decay hs) hscaled.summable
    _ = q * (2 : ℝ) ^ (2 - s.re) := hscaled.tsum_eq

private lemma tail_q_nonneg : 0 ≤ q := by
  have h := norm_zeta_sub_one_decay (s := (2 : ℂ)) (by norm_num)
  have h0 := (norm_nonneg (riemannZeta (2 : ℂ) - 1)).trans h
  simpa using h0

private lemma tail_q_lt_one : q < 1 := by
  have h :=
    ConjectureMachines.Semantics.Riemann.VonMangoldtCount.pi_sq_div_six_sub_one_le_three_fourths
  linarith

private lemma norm_zeta_sub_one_le_q {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ q := by
  have hp : (2 : ℝ) ^ (2 - s.re) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by linarith : 2 - s.re ≤ 0)
  exact (norm_zeta_sub_one_decay hs).trans
    (by simpa using mul_le_mul_of_nonneg_left hp tail_q_nonneg)

lemma re_zeta_pos_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    0 < (riemannZeta s).re := by
  have ha := (Complex.abs_re_le_norm (riemannZeta s - 1)).trans
    (norm_zeta_sub_one_le_q hs)
  have hb := (abs_le.mp ha).1
  simp only [Complex.sub_re, Complex.one_re] at hb
  linarith [tail_q_lt_one]

private lemma differentiableAt_principal_log_zeta {s : ℂ} (hs : 2 ≤ s.re) :
    DifferentiableAt ℂ (fun z ↦ Complex.log (riemannZeta z)) s := by
  have hs1 : s ≠ 1 := by
    intro he
    have hre : s.re = 1 := by simpa using congrArg Complex.re he
    linarith
  exact (Complex.hasDerivAt_log (Or.inl (re_zeta_pos_of_two_le_re hs))).differentiableAt.comp s
    (differentiableAt_riemannZeta hs1)

/-- Uniform exponential bound for the actual principal logarithm in the closed
right half-plane. The coefficient is q/(1-q), q = pi^2/6-1. -/
theorem norm_log_riemannZeta_le_rpow {s : ℂ} (hs : 2 ≤ s.re) :
    ‖Complex.log (riemannZeta s)‖ ≤ Ctail * (2 : ℝ) ^ (2 - s.re) := by
  have hwq := norm_zeta_sub_one_le_q hs
  have hw : ‖riemannZeta s - 1‖ < 1 := hwq.trans_lt tail_q_lt_one
  have ht := Complex.norm_log_sub_logTaylor_le 0 hw
  have hone : (1 : ℂ) + (riemannZeta s - 1) = riemannZeta s := by ring
  rw [hone] at ht
  have hlog : ‖Complex.log (riemannZeta s)‖ ≤
      ‖riemannZeta s - 1‖ / (1 - ‖riemannZeta s - 1‖) := by
    simpa [Complex.logTaylor, div_eq_mul_inv] using ht
  have hd : 0 < 1 - q := sub_pos.mpr tail_q_lt_one
  calc
    ‖Complex.log (riemannZeta s)‖ ≤
        ‖riemannZeta s - 1‖ / (1 - ‖riemannZeta s - 1‖) := hlog
    _ ≤ ‖riemannZeta s - 1‖ / (1 - q) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hd (by linarith)
    _ ≤ (q * (2 : ℝ) ^ (2 - s.re)) / (1 - q) :=
      div_le_div_of_nonneg_right (norm_zeta_sub_one_decay hs) hd.le
    _ = Ctail * (2 : ℝ) ^ (2 - s.re) := by ring

private lemma continuousOn_horizontal_principal_log {R : ℝ} (hR : 2 ≤ R) (t : ℝ) :
    ContinuousOn (fun σ : ℝ ↦ Complex.log (riemannZeta ((σ : ℂ) + (t : ℂ) * I))) (Ici R) := by
  intro σ hσ
  have hs : 2 ≤ ((σ : ℂ) + (t : ℂ) * I).re := by simpa using hR.trans hσ
  exact ((differentiableAt_principal_log_zeta hs).continuousAt.comp
    (f := fun x : ℝ ↦ (x : ℂ) + (t : ℂ) * I)
    (show ContinuousAt (fun x : ℝ ↦ (x : ℂ) + (t : ℂ) * I) σ by fun_prop)).continuousWithinAt

private lemma continuous_vertical_principal_log {R : ℝ} (hR : 2 ≤ R) :
    Continuous (fun t : ℝ ↦ Complex.log (riemannZeta ((R : ℂ) + (t : ℂ) * I))) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs : 2 ≤ ((R : ℂ) + (t : ℂ) * I).re := by simpa using hR
  exact (differentiableAt_principal_log_zeta hs).continuousAt.comp
    (f := fun y : ℝ ↦ (R : ℂ) + (y : ℂ) * I)
    (show ContinuousAt (fun y : ℝ ↦ (R : ℂ) + (y : ℂ) * I) t by fun_prop)

private lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

private lemma two_rpow_decay_eq (σ : ℝ) :
    (2 : ℝ) ^ (2 - σ) = Real.exp (2 * Real.log 2) * Real.exp ((-Real.log 2) * σ) := by
  rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_add]
  congr 1; ring

private lemma integrableOn_tail_majorant (R : ℝ) :
    IntegrableOn (fun σ : ℝ ↦ Ctail * (2 : ℝ) ^ (2 - σ)) (Ioi R) := by
  have h := (integrableOn_exp_mul_Ioi (by linarith [log_two_pos] : -Real.log 2 < 0) R).const_mul
    (Ctail * Real.exp (2 * Real.log 2))
  simpa only [IntegrableOn, two_rpow_decay_eq, mul_assoc] using h

private lemma integral_tail_majorant (R : ℝ) :
    (∫ σ : ℝ in Ioi R, Ctail * (2 : ℝ) ^ (2 - σ)) =
      Ctail / Real.log 2 * (2 : ℝ) ^ (2 - R) := by
  calc
    (∫ σ : ℝ in Ioi R, Ctail * (2 : ℝ) ^ (2 - σ)) =
        (Ctail * Real.exp (2 * Real.log 2)) *
          (∫ σ : ℝ in Ioi R, Real.exp ((-Real.log 2) * σ)) := by
      simp_rw [two_rpow_decay_eq, ← mul_assoc]
      rw [MeasureTheory.integral_const_mul]
    _ = Ctail / Real.log 2 * (2 : ℝ) ^ (2 - R) := by
      rw [integral_exp_mul_Ioi (by linarith [log_two_pos] : -Real.log 2 < 0),
        two_rpow_decay_eq]
      simp only [neg_div_neg_eq]
      ring

/-- Bochner integrability of the actual complex principal-log tail. -/
theorem integrableOn_principal_log_riemannZeta_Ioi {R : ℝ} (hR : 2 ≤ R) (t : ℝ) :
    IntegrableOn
      (fun σ : ℝ ↦ Complex.log (riemannZeta ((σ : ℂ) + (t : ℂ) * I))) (Ioi R) := by
  refine (integrableOn_tail_majorant R).mono'
    (((continuousOn_horizontal_principal_log hR t).mono Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  simpa using norm_log_riemannZeta_le_rpow
    (s := (σ : ℂ) + (t : ℂ) * I) (by simpa using hR.trans (le_of_lt hσ))

/-- Absolute integrability of the real logarithm of the actual zeta norm. -/
theorem integrableOn_log_norm_riemannZeta_Ioi {R : ℝ} (hR : 2 ≤ R) (t : ℝ) :
    IntegrableOn
      (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖) (Ioi R) := by
  simpa only [RCLike.re_to_complex, Complex.log_re] using
    (integrableOn_principal_log_riemannZeta_Ioi hR t).re

/-- Uniform, explicit absolute principal-log tail estimate for every real height. -/
theorem integral_norm_principal_log_riemannZeta_Ioi_le {R : ℝ} (hR : 2 ≤ R) (t : ℝ) :
    (∫ σ : ℝ in Ioi R, ‖Complex.log (riemannZeta ((σ : ℂ) + (t : ℂ) * I))‖) ≤
      Ctail / Real.log 2 * (2 : ℝ) ^ (2 - R) := by
  calc
    (∫ σ : ℝ in Ioi R, ‖Complex.log (riemannZeta ((σ : ℂ) + (t : ℂ) * I))‖) ≤
        ∫ σ : ℝ in Ioi R, Ctail * (2 : ℝ) ^ (2 - σ) := by
      apply integral_mono_ae (integrableOn_principal_log_riemannZeta_Ioi hR t).norm
        (integrableOn_tail_majorant R)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
      simpa using norm_log_riemannZeta_le_rpow
        (s := (σ : ℂ) + (t : ℂ) * I) (by simpa using hR.trans (le_of_lt hσ))
    _ = Ctail / Real.log 2 * (2 : ℝ) ^ (2 - R) := integral_tail_majorant R

/-- The same uniform estimate for the absolute real lognorm tail. -/
theorem integral_abs_log_norm_riemannZeta_Ioi_le {R : ℝ} (hR : 2 ≤ R) (t : ℝ) :
    (∫ σ : ℝ in Ioi R, |Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖|) ≤
      Ctail / Real.log 2 * (2 : ℝ) ^ (2 - R) := by
  apply le_trans _ (integral_norm_principal_log_riemannZeta_Ioi_le hR t)
  apply integral_mono_ae (integrableOn_log_norm_riemannZeta_Ioi hR t).abs
    (integrableOn_principal_log_riemannZeta_Ioi hR t).norm
  exact Filter.Eventually.of_forall fun σ ↦ by
    simpa only [Complex.log_re] using
      Complex.abs_re_le_norm (Complex.log (riemannZeta ((σ : ℂ) + (t : ℂ) * I)))

/-- The actual improper horizontal lognorm tail, with lower endpoint R. -/
def zetaHorizontalLogTail (R t : ℝ) : ℝ :=
  ∫ σ : ℝ in Ioi R, Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖

/-- An explicit truncation error for the actual tail and its finite interval integral. -/
theorem abs_zetaHorizontalLogTail_sub_intervalIntegral_le {R X : ℝ}
    (hR : 2 ≤ R) (hRX : R ≤ X) (t : ℝ) :
    |zetaHorizontalLogTail R t -
      (∫ σ : ℝ in R..X, Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖)| ≤
      Ctail / Real.log 2 * (2 : ℝ) ^ (2 - X) := by
  have he : zetaHorizontalLogTail R t - zetaHorizontalLogTail X t =
      ∫ σ : ℝ in R..X, Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ :=
    intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_log_norm_riemannZeta_Ioi hR t) hRX
  have he' : zetaHorizontalLogTail R t -
      (∫ σ : ℝ in R..X, Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖) =
        zetaHorizontalLogTail X t := by linarith
  rw [he']
  calc
    |zetaHorizontalLogTail X t| ≤
        ∫ σ : ℝ in Ioi X, |Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖| := by
      simpa only [zetaHorizontalLogTail, Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖)
          (μ := volume.restrict (Ioi X)))
    _ ≤ Ctail / Real.log 2 * (2 : ℝ) ^ (2 - X) :=
      integral_abs_log_norm_riemannZeta_Ioi_le (hR.trans hRX) t

private lemma horizontal_principal_log_intervalIntegrable {R X : ℝ}
    (hR : 2 ≤ R) (hRX : R ≤ X) (t : ℝ) :
    IntervalIntegrable
      (fun σ : ℝ ↦ Complex.log (riemannZeta ((σ : ℂ) + (t : ℂ) * I))) volume R X := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hRX]
  exact (continuousOn_horizontal_principal_log hR t).mono Icc_subset_Ici_self

private lemma finite_horizontal_log_transport {R X : ℝ} (hR : 2 ≤ R) (hRX : R ≤ X)
    (u v : ℝ) :
    (∫ σ : ℝ in R..X, Real.log ‖riemannZeta ((σ : ℂ) + (v : ℂ) * I)‖) -
        (∫ σ : ℝ in R..X, Real.log ‖riemannZeta ((σ : ℂ) + (u : ℂ) * I)‖) =
      ∫ t : ℝ in u..v,
        (Complex.log (riemannZeta ((R : ℂ) + (t : ℂ) * I))).im -
          (Complex.log (riemannZeta ((X : ℂ) + (t : ℂ) * I))).im := by
  let L : ℂ → ℂ := fun z ↦ Complex.log (riemannZeta z)
  have hd : DifferentiableOn ℂ L
      (uIcc (((R : ℂ) + (u : ℂ) * I).re) (((X : ℂ) + (v : ℂ) * I).re) ×ℂ
        uIcc (((R : ℂ) + (u : ℂ) * I).im) (((X : ℂ) + (v : ℂ) * I).im)) := by
    intro s hs
    have hσ : s.re ∈ uIcc R X := by simpa using (mem_reProdIm.mp hs).1
    rw [uIcc_of_le hRX] at hσ
    exact (differentiableAt_principal_log_zeta (hR.trans hσ.1)).differentiableWithinAt
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn L
    ((R : ℂ) + (u : ℂ) * I) ((X : ℂ) + (v : ℂ) * I) hd
  simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im,
    mul_zero, sub_zero, zero_add, add_zero, mul_one, smul_eq_mul] at hcauchy
  have hr := congrArg Complex.re hcauchy
  simp only [add_re, sub_re, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub,
    zero_re] at hr
  have hXu := (continuous_vertical_principal_log (hR.trans hRX)).intervalIntegrable
    (μ := volume) u v
  have hRu := (continuous_vertical_principal_log hR).intervalIntegrable (μ := volume) u v
  have hXim := (RCLike.imCLM : ℂ →L[ℝ] ℝ).intervalIntegral_comp_comm hXu
  have hRim := (RCLike.imCLM : ℂ →L[ℝ] ℝ).intervalIntegral_comp_comm hRu
  have hure := (RCLike.reCLM : ℂ →L[ℝ] ℝ).intervalIntegral_comp_comm
    (horizontal_principal_log_intervalIntegrable hR hRX u)
  have hvre := (RCLike.reCLM : ℂ →L[ℝ] ℝ).intervalIntegral_comp_comm
    (horizontal_principal_log_intervalIntegrable hR hRX v)
  change (∫ σ : ℝ in R..X, (L ((σ : ℂ) + (u : ℂ) * I)).re) =
    (∫ σ : ℝ in R..X, L ((σ : ℂ) + (u : ℂ) * I)).re at hure
  change (∫ σ : ℝ in R..X, (L ((σ : ℂ) + (v : ℂ) * I)).re) =
    (∫ σ : ℝ in R..X, L ((σ : ℂ) + (v : ℂ) * I)).re at hvre
  change (∫ t : ℝ in u..v, (L ((X : ℂ) + (t : ℂ) * I)).im) =
    (∫ t : ℝ in u..v, L ((X : ℂ) + (t : ℂ) * I)).im at hXim
  change (∫ t : ℝ in u..v, (L ((R : ℂ) + (t : ℂ) * I)).im) =
    (∫ t : ℝ in u..v, L ((R : ℂ) + (t : ℂ) * I)).im at hRim
  rw [← hure, ← hvre, ← hXim, ← hRim] at hr
  simp only [L, Complex.log_re] at hr
  have hRi : IntervalIntegrable
      (fun t : ℝ ↦ (Complex.log (riemannZeta ((R : ℂ) + (t : ℂ) * I))).im)
      volume u v :=
    (Complex.continuous_im.comp (continuous_vertical_principal_log hR)).intervalIntegrable u v
  have hXi : IntervalIntegrable
      (fun t : ℝ ↦ (Complex.log (riemannZeta ((X : ℂ) + (t : ℂ) * I))).im)
      volume u v :=
    (Complex.continuous_im.comp
      (continuous_vertical_principal_log (hR.trans hRX))).intervalIntegrable u v
  rw [intervalIntegral.integral_sub hRi hXi]
  linarith

private lemma tendsto_two_rpow_decay :
    Tendsto (fun X : ℝ ↦ (2 : ℝ) ^ (2 - X)) atTop (𝓝 0) := by
  have he : Tendsto (fun X : ℝ ↦ Real.exp ((-Real.log 2) * X)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop
        (by linarith [log_two_pos] : -Real.log 2 < 0) tendsto_id)
  simpa only [two_rpow_decay_eq, mul_zero] using he.const_mul (Real.exp (2 * Real.log 2))

private lemma tendsto_height_edge_integral_zero (u v : ℝ) :
    Tendsto
      (fun X : ℝ ↦ ∫ t : ℝ in u..v,
        (Complex.log (riemannZeta ((X : ℂ) + (t : ℂ) * I))).im) atTop (𝓝 0) := by
  apply squeeze_zero_norm'
    (a := fun X : ℝ ↦ (Ctail * (2 : ℝ) ^ (2 - X)) * |v - u|)
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t _
    simpa using
      (Complex.abs_im_le_norm (Complex.log (riemannZeta ((X : ℂ) + (t : ℂ) * I)))).trans
        (norm_log_riemannZeta_le_rpow (by simpa using hX))
  · simpa only [mul_zero, zero_mul] using
      (tendsto_two_rpow_decay.const_mul Ctail).mul_const |v - u|

/-- Oriented height transport of the actual improper tail. The right-hand side
keeps the imaginary part inside the real interval integral, for all u and v. -/
theorem zetaHorizontalLogTail_sub_eq_intervalIntegral {R : ℝ} (hR : 2 ≤ R) (u v : ℝ) :
    zetaHorizontalLogTail R v - zetaHorizontalLogTail R u =
      ∫ t : ℝ in u..v, (Complex.log (riemannZeta ((R : ℂ) + (t : ℂ) * I))).im := by
  have hv := MeasureTheory.intervalIntegral_tendsto_integral_Ioi R
    (integrableOn_log_norm_riemannZeta_Ioi hR v) (tendsto_id : Tendsto (fun X : ℝ ↦ X) atTop atTop)
  have hu := MeasureTheory.intervalIntegral_tendsto_integral_Ioi R
    (integrableOn_log_norm_riemannZeta_Ioi hR u) (tendsto_id : Tendsto (fun X : ℝ ↦ X) atTop atTop)
  have hleft : Tendsto
      (fun X : ℝ ↦
        (∫ σ : ℝ in R..X, Real.log ‖riemannZeta ((σ : ℂ) + (v : ℂ) * I)‖) -
        (∫ σ : ℝ in R..X, Real.log ‖riemannZeta ((σ : ℂ) + (u : ℂ) * I)‖))
      atTop (𝓝 (zetaHorizontalLogTail R v - zetaHorizontalLogTail R u)) := hv.sub hu
  have hright : Tendsto
      (fun X : ℝ ↦ ∫ t : ℝ in u..v,
        (Complex.log (riemannZeta ((R : ℂ) + (t : ℂ) * I))).im -
        (Complex.log (riemannZeta ((X : ℂ) + (t : ℂ) * I))).im)
      atTop (𝓝 (∫ t : ℝ in u..v,
        (Complex.log (riemannZeta ((R : ℂ) + (t : ℂ) * I))).im)) := by
    have ht := (tendsto_height_edge_integral_zero u v).const_sub
      (∫ t : ℝ in u..v, (Complex.log (riemannZeta ((R : ℂ) + (t : ℂ) * I))).im)
    simp only [sub_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
    exact (intervalIntegral.integral_sub
      ((Complex.continuous_im.comp (continuous_vertical_principal_log hR)).intervalIntegrable u v)
      ((Complex.continuous_im.comp (continuous_vertical_principal_log hX)).intervalIntegrable
        u v)).symm
  have heq :
      (fun X : ℝ ↦
        (∫ σ : ℝ in R..X, Real.log ‖riemannZeta ((σ : ℂ) + (v : ℂ) * I)‖) -
        (∫ σ : ℝ in R..X, Real.log ‖riemannZeta ((σ : ℂ) + (u : ℂ) * I)‖)) =ᶠ[atTop]
      (fun X : ℝ ↦ ∫ t : ℝ in u..v,
        (Complex.log (riemannZeta ((R : ℂ) + (t : ℂ) * I))).im -
        (Complex.log (riemannZeta ((X : ℂ) + (t : ℂ) * I))).im) := by
    filter_upwards [eventually_ge_atTop R] with X hX
    exact finite_horizontal_log_transport hR hX u v
  exact tendsto_nhds_unique (hleft.congr' heq) hright

end Zeta23.RvM
