/- GID: D5/S3/Analytic/Fourier/ThetaDifferentialKernel
   generality: I
   mirror-B: D5/B/S3/Analytic/Fourier/ThetaDifferentialKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Differentiate the original theta series with locally summable majorants. -/

import D5.S3.Zeros.Jensen.SourceThetaMomentBounds
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Analysis.Calculus.SmoothSeries

noncomputable section
namespace D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open Real Set Filter Topology
open D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering

/-- Jacobi's theta function on the positive real axis. -/
def theta (t : ℝ) : ℝ := HurwitzZeta.evenKernel 0 t

/-- The polynomially weighted positive-index theta series. -/
def thetaSeries (k : ℕ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) ^ k * exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t)

/-- Romik's original differential weight. -/
def omega (t : ℝ) : ℝ :=
  ∑' n : ℕ, (2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * t ^ 2 -
    3 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * t) *
    exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * t)

/-- The original kernel, with no absolute value in its argument. -/
def romikPhi (x : ℝ) : ℝ := 2 * exp (x / 2) * omega (exp (2 * x))

/-- The rescaled theta tail whose differential operator gives the kernel. -/
def psi (x : ℝ) : ℝ := exp (x / 2) * (theta (exp (2 * x)) - 1) / 2

/-- The imported Gaussian-series convergence holds at every positive parameter. -/
theorem thetaSeries_summable (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k *
      exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t)) :=
  HurwitzKernelBounds.summable_f_nat k 1 ht

/-- A summable majorant, uniform on the ray above any positive lower endpoint. -/
theorem thetaSeries_local_majorant (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => Real.pi * (((n : ℝ) + 1) ^ (k + 2) *
      exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * a))) ∧
    ∀ n : ℕ, ∀ t : ℝ, a ≤ t →
      ‖-Real.pi * (((n : ℝ) + 1) ^ (k + 2) *
        exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t))‖ ≤
      Real.pi * (((n : ℝ) + 1) ^ (k + 2) *
        exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * a)) := by
  refine ⟨(thetaSeries_summable (k + 2) ha).mul_left Real.pi, ?_⟩
  intro n t ht
  rw [norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos pi_pos,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left ht
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr pi_pos.le) (sq_nonneg _))

private theorem term_hasDerivAt (k n : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => ((n : ℝ) + 1) ^ k *
      exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t))
      (-Real.pi * (((n : ℝ) + 1) ^ (k + 2) *
        exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t))) t := by
  convert! ((hasDerivAt_id t).const_mul (-Real.pi * ((n : ℝ) + 1) ^ 2)).exp.const_mul
    (((n : ℝ) + 1) ^ k) using 1 <;> simp only [pow_add, id_eq, mul_one] <;> ring

/-- Termwise differentiation is justified by the explicit local majorant. -/
theorem hasDerivAt_thetaSeries (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (thetaSeries k) (-Real.pi * thetaSeries (k + 2) t) t := by
  obtain ⟨hs, hb⟩ := thetaSeries_local_majorant k (half_pos ht)
  have h := hasDerivAt_tsum_of_isPreconnected hs isOpen_Ioi (convex_Ioi (t / 2)).isPreconnected
    (fun n y _ => term_hasDerivAt k n y)
    (fun n y hy => hb n y (le_of_lt hy))
    (show t ∈ Ioi (t / 2) by simp only [mem_Ioi]; linarith)
    (thetaSeries_summable k ht)
    (show t ∈ Ioi (t / 2) by simp only [mem_Ioi]; linarith)
  simpa only [thetaSeries, tsum_mul_left] using! h

/-- The zeroth weighted series is exactly half of the actual theta tail. -/
theorem thetaSeries_zero {t : ℝ} (ht : 0 < t) :
    thetaSeries 0 t = (theta t - 1) / 2 := by
  have h := (HurwitzZeta.hasSum_nat_cosKernel₀ 0 ht).mul_left (1 / 2 : ℝ)
  simp only [mul_zero, zero_mul, cos_zero, mul_one] at h
  have h' : HasSum (fun n : ℕ => exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t))
      ((theta t - 1) / 2) := by
    simpa only [theta, HurwitzZeta.evenKernel_eq_cosKernel_of_zero, ← mul_assoc,
      one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_mul, div_eq_mul_inv, AddCircle.coe_zero,
      mul_comm] using! h
  simpa only [thetaSeries, pow_zero, one_mul] using h'.tsum_eq

/-- The rescaled theta tail has its literal positive-index series representation. -/
theorem psi_eq_series (x : ℝ) : psi x = exp (x / 2) * thetaSeries 0 (exp (2 * x)) := by
  rw [thetaSeries_zero (exp_pos _), psi, mul_div_assoc]

/-- The original differential weight expressed in two convergent weighted series. -/
theorem omega_eq_series {t : ℝ} (ht : 0 < t) :
    omega t = 2 * Real.pi ^ 2 * t ^ 2 * thetaSeries 4 t -
      3 * Real.pi * t * thetaSeries 2 t := by
  unfold omega thetaSeries
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_sub ((thetaSeries_summable 4 ht).mul_left _) 
      ((thetaSeries_summable 2 ht).mul_left _)]
  apply tsum_congr
  intro n
  push_cast
  ring

end D5.S3.Analytic.Fourier.ThetaDifferentialKernel
