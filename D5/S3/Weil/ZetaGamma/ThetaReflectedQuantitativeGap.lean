/- GID: D5/S3/Weil/ZetaGamma/ThetaReflectedQuantitativeGap
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/ThetaReflectedQuantitativeGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative reflected theta-kernel gap from the square-variable curvature reserve. -/
/- Quantitative consumer of the already paid full-theta fourth-log reserve.
   This fragment is intentionally separate from the pointwise W12 theorem:
   it adds a polynomial correction to the square-variable logarithm and
   derives a lower bound for the reflected gap. It makes no PSD or RH claim. -/

import D5.S3.Weil.ZetaGamma.ThetaReflectedKernelComparison
import D5.S3.Analytic.Fourier.ThetaQuantitativeCurvature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Batteries.Tactic.OpenPrivate

noncomputable section
namespace D5.S3.Weil.ZetaGamma.ThetaReflectedKernelComparison

open Real Set MeasureTheory Filter
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Analytic.Fourier.ThetaRadialCurvature
open private p d radialStart spread spread_geometry radialProduct radialIntegrand offsetProduct pd_geometry
  strictConcave_symmetric_sum log_square_pair phi_pos
  from D5.S3.Weil.ZetaGamma.ThetaReflectedKernelComparison

private theorem strong_symmetric_log_gap {h : ℝ → ℝ}
    (hh : StrictConcaveOn ℝ (Ioi (0 : ℝ)) (fun z => h z + z ^ 2 / 48))
    {r s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (htr : t < r) :
    h (r - t) + h (r + t) + (t ^ 2 - s ^ 2) / 24 <
      h (r - s) + h (r + s) := by
  have hpair := strictConcave_symmetric_sum hh hs hst htr
  have ht : 0 < t := hs.trans_lt hst
  have hden : 0 < 48 := by norm_num
  nlinarith [hpair]

private theorem radial_product_gap {c q r : ℝ}
    (hc : 0 ≤ c) (hcq : c < q) (hr : q ^ 2 + c ^ 2 < r)
    (hne : r ≠ 2 * q ^ 2) :
    radialProduct q r * ((q ^ 2 - c ^ 2) * (r - (q ^ 2 + c ^ 2)) / 6) <
      radialProduct c r - radialProduct q r := by
  have hq : 0 < q := hc.trans_lt hcq
  have hrc : c ^ 2 < r := by nlinarith [sq_nonneg q]
  have hrq : q ^ 2 < r := by nlinarith [sq_nonneg c]
  have hsp := spread_geometry hc hcq hr hne
  have hstrong := RhTransient.ThetaQuantitativeCurvature.actual_square_strong_concavity
  have hlog := strong_symmetric_log_gap hstrong hsp.1 hsp.2.1 hsp.2.2
  rw [log_square_pair q r hrq, log_square_pair c r hrc] at hlog
  have hdelta : 0 < (q ^ 2 - c ^ 2) * (r - (q ^ 2 + c ^ 2)) / 6 := by
    have hbase : 0 < q ^ 2 - c ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hcq) (by linarith : 0 < q + c)]
    positivity
  have hlog' : log (radialProduct q r) +
      ((q ^ 2 - c ^ 2) * (r - (q ^ 2 + c ^ 2)) / 6) <
      log (radialProduct c r) := by
    have hsq_q : sqrt (r - q ^ 2) ^ 2 = r - q ^ 2 :=
      sq_sqrt (by nlinarith [hrq])
    have hsq_c : sqrt (r - c ^ 2) ^ 2 = r - c ^ 2 :=
      sq_sqrt (by nlinarith [hrc])
    have hdelta_eq :
        (spread q r ^ 2 - spread c r ^ 2) / 24 =
          (q ^ 2 - c ^ 2) * (r - (q ^ 2 + c ^ 2)) / 6 := by
      dsimp [spread]
      calc
        _ = (4 * q ^ 2 * sqrt (r - q ^ 2) ^ 2 -
            4 * c ^ 2 * sqrt (r - c ^ 2) ^ 2) / 24 := by ring
        _ = _ := by
          rw [hsq_q, hsq_c]
          ring
    simp only [radialProduct, offsetProduct,
      log_mul (phi_pos _).ne' (phi_pos _).ne']
    rw [hdelta_eq] at hlog
    simpa only [add_comm, add_left_comm, add_assoc] using hlog
  have hexp := exp_lt_exp.mpr hlog'
  have hpq : 0 < radialProduct q r := mul_pos (phi_pos _) (phi_pos _)
  have hpc : 0 < radialProduct c r := mul_pos (phi_pos _) (phi_pos _)
  simp only [exp_add, exp_log hpq, exp_log hpc] at hexp
  have hadd := Real.add_one_le_exp ((q ^ 2 - c ^ 2) * (r - (q ^ 2 + c ^ 2)) / 6)
  have hmul := mul_le_mul_of_nonneg_left hadd hpq.le
  have hmul' : radialProduct q r *
      (1 + ((q ^ 2 - c ^ 2) * (r - (q ^ 2 + c ^ 2)) / 6)) ≤
      radialProduct q r * exp ((q ^ 2 - c ^ 2) * (r - (q ^ 2 + c ^ 2)) / 6) := by
    simpa only [add_comm] using hmul
  have hstrict : radialProduct q r *
      (1 + ((q ^ 2 - c ^ 2) * (r - (q ^ 2 + c ^ 2)) / 6)) <
      radialProduct c r := lt_of_le_of_lt hmul' hexp
  linarith

/-- Pointwise reflected deficit with an explicit quadratic separation factor. -/
theorem radial_integrand_gap_quantitative {v c q r : ℝ} (hv : 0 ≤ v)
    (hc : 0 ≤ c) (hcq : c < q) (hr : q ^ 2 + c ^ 2 < r)
    (hne : r ≠ 2 * q ^ 2) :
    radialIntegrand v q r +
        radialIntegrand v q r *
          ((q ^ 2 - c ^ 2) * (r - (q ^ 2 + c ^ 2)) / 6) <
      radialIntegrand v c r := by
  have hprod := radial_product_gap hc hcq hr hne
  have hprod' : radialProduct q r + radialProduct q r *
      ((q ^ 2 - c ^ 2) * (r - (q ^ 2 + c ^ 2)) / 6) < radialProduct c r := by
    linarith
  have hcosh : cosh (2 * v * sqrt (r - q ^ 2)) ≤
      cosh (2 * v * sqrt (r - c ^ 2)) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt (by nlinarith [sq_nonneg q, sq_nonneg c])) (by positivity)
  have hcp : 0 < cosh (2 * v * sqrt (r - q ^ 2)) := cosh_pos _
  have hcc : 0 ≤ cosh (2 * v * sqrt (r - c ^ 2)) := (cosh_pos _).le
  have hpq : 0 < radialProduct q r := mul_pos (phi_pos _) (phi_pos _)
  have hpc : 0 < radialProduct c r := mul_pos (phi_pos _) (phi_pos _)
  dsimp only [radialIntegrand]
  calc
    _ = cosh (2 * v * sqrt (r - q ^ 2)) *
        (radialProduct q r + radialProduct q r *
          ((q ^ 2 - c ^ 2) * (r - (q ^ 2 + c ^ 2)) / 6)) := by ring
    _ < cosh (2 * v * sqrt (r - q ^ 2)) * radialProduct c r :=
      mul_lt_mul_of_pos_left hprod' hcp
    _ ≤ cosh (2 * v * sqrt (r - c ^ 2)) * radialProduct c r :=
      mul_le_mul_of_nonneg_right hcosh hpc.le

theorem physical_kernel_gap_quantitative {a b v : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hv : 0 ≤ v) {r : ℝ}
    (hr : radialStart a b < r) (hne : r ≠ 2 * (p a b) ^ 2) :
    radialIntegrand v (p a b) r +
        radialIntegrand v (p a b) r *
          (a * b * (r - radialStart a b) / 6) <
      radialIntegrand v (d a b) r := by
  have hpd := pd_geometry ha hb
  have hq2 : (p a b) ^ 2 - (d a b) ^ 2 = a * b := by
    dsimp [p, d]
    have habs : |a - b| ^ 2 = (a - b) ^ 2 := sq_abs (a - b)
    rw [div_pow, div_pow, habs]
    ring
  have h := radial_integrand_gap_quantitative hv hpd.1 hpd.2 hr hne
  rw [hq2] at h
  simpa only [radialStart] using h

end D5.S3.Weil.ZetaGamma.ThetaReflectedKernelComparison
