/- GID: D5/S3/Analytic/PowerSeries/CdsoAllocationGerms
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual analytic allocation germs and their quadratic Taylor cutoff. -/

import D5.S3.Analytic.PowerSeries.RadicalMultiplicity
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Data.Nat.Choose.Cast

/-! Actual real functions and their genuine Taylor series at zero. -/

noncomputable section
open Filter Set Polynomial
open scoped Topology PowerSeries

namespace CdsoPeriodic

/-- The genuine Taylor coefficients of a real function at zero. -/
def taylor (f : ℝ → ℝ) : ℝ⟦X⟧ :=
  PowerSeries.mk fun n => iteratedDeriv n f 0 / n.factorial

private theorem taylor_congr {f g : ℝ → ℝ} (h : f =ᶠ[𝓝 0] g) : taylor f = taylor g := by
  ext n
  simp only [taylor, PowerSeries.coeff_mk, h.iteratedDeriv_eq n]

private theorem taylor_add {f g : ℝ → ℝ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) :
    taylor (fun u => f u + g u) = taylor f + taylor g := by
  ext n
  simp only [taylor, PowerSeries.coeff_mk, map_add,
    iteratedDeriv_add hf.contDiffAt hg.contDiffAt, add_div]

private theorem taylor_mul {f g : ℝ → ℝ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) :
    taylor (fun u => f u * g u) = taylor f * taylor g := by
  ext n
  simp only [taylor, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_choose ℝ (by simpa using Finset.mem_range.mp hi)]
  field_simp
  <;> ring

private theorem taylor_const (c : ℝ) : taylor (fun _ => c) = PowerSeries.C c := by
  ext n
  cases n with
  | zero => simp [taylor]
  | succ n => simp [taylor, iteratedDeriv_succ]

private theorem taylor_id : taylor (fun u : ℝ => u) = PowerSeries.X := by
  ext n
  simp [taylor, iteratedDeriv_id, PowerSeries.coeff_X]

private theorem taylor_poly (p : ℝ[X]) : taylor p.eval = (p : ℝ⟦X⟧) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add, Polynomial.coe_add, hp, hq] using
      taylor_add (p.analyticAt) (q.analyticAt)
  | monomial n c =>
    have hx (k : ℕ) : taylor (fun u : ℝ => u ^ k) = PowerSeries.X ^ k := by
      induction k with
      | zero => simpa using taylor_const 1
      | succ k ih =>
        simpa only [pow_succ, ih, taylor_id] using
          taylor_mul (f := fun u : ℝ => u ^ k) (g := fun u : ℝ => u)
            (by fun_prop) (by fun_prop)
    simpa only [Polynomial.eval_monomial, Polynomial.coe_monomial,
      PowerSeries.monomial_eq_C_mul_X_pow, taylor_const, hx] using
      taylor_mul (f := fun _ : ℝ => c) (g := fun u : ℝ => u ^ n)
        (by fun_prop) (by fun_prop)

private theorem taylor_eq_zero_iff {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    taylor f = 0 ↔ f =ᶠ[𝓝 0] 0 := by
  constructor
  · intro h
    have hp := hf.hasFPowerSeriesAt
    have hs : FormalMultilinearSeries.ofScalars ℝ
        (fun n => iteratedDeriv n f 0 / n.factorial) = 0 := by
      ext n v
      have hc := congrArg (PowerSeries.coeff n) h
      simp only [taylor, PowerSeries.coeff_mk, map_zero] at hc
      simp [FormalMultilinearSeries.ofScalars, hc]
    rw [hs] at hp
    exact hp.eventually_eq_zero
  · intro h
    rw [taylor_congr h, taylor_const]
    simp

private theorem analytic_sqrt {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) (h0 : 0 < f 0) :
    AnalyticAt ℝ (fun u => Real.sqrt (f u)) 0 := by
  have hbase : AnalyticAt ℝ (fun y : ℝ => Real.sqrt (1 + y)) 0 := by
    simpa only [Real.sqrt_eq_rpow] using
      (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := (1 : ℝ) / 2)).analyticAt
  have hg : AnalyticAt ℝ (fun u => f u / f 0 - 1) 0 :=
    hf.div_const.sub analyticAt_const
  have hg0 : f 0 / f 0 - 1 = 0 := by simp [ne_of_gt h0]
  have hh := (hbase.comp 0 (hg0 ▸ hg)).const_mul (Real.sqrt (f 0))
  convert hh using 1
  funext u
  rw [← Real.sqrt_mul h0.le]
  congr 1
  field_simp
  <;> ring

/-- Source radical quotient with the positive real square root. -/
def radicalR (b δ k u : ℝ) : ℝ :=
  Real.sqrt ((b + δ * u) ^ 2 + k ^ 2 * u ^ 2) / (b + δ * u) - 1

/-- Rationalized removable extension of the quotient by the square of the parameter. -/
def radicalExtension (b δ k u : ℝ) : ℝ :=
  k ^ 2 / ((b + δ * u) *
    (Real.sqrt ((b + δ * u) ^ 2 + k ^ 2 * u ^ 2) + (b + δ * u)))

private theorem radical_rationalization (b δ k u : ℝ) (hb : 0 < b + δ * u) :
    radicalR b δ k u = u ^ 2 * radicalExtension b δ k u := by
  have hp : 0 ≤ (b + δ * u) ^ 2 + k ^ 2 * u ^ 2 := by positivity
  have hs := Real.sq_sqrt hp
  have hden : Real.sqrt ((b + δ * u) ^ 2 + k ^ 2 * u ^ 2) + (b + δ * u) ≠ 0 := by
    positivity
  unfold radicalR radicalExtension
  field_simp
  <;> nlinarith

private theorem analytic_radicalExtension (b δ k : ℝ) (hb : 0 < b) :
    AnalyticAt ℝ (radicalExtension b δ k) 0 := by
  have hpoly : AnalyticAt ℝ (fun u : ℝ => (b + δ * u) ^ 2 + k ^ 2 * u ^ 2) 0 := by
    fun_prop
  have hpos : 0 < (b + δ * (0 : ℝ)) ^ 2 + k ^ 2 * (0 : ℝ) ^ 2 := by
    simpa using sq_pos_of_pos hb
  apply analyticAt_const.div
    (((by fun_prop : AnalyticAt ℝ (fun u : ℝ => b + δ * u) 0)).mul
      ((analytic_sqrt hpoly hpos).add (by fun_prop)))
  simp only [mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)]
  positivity

end CdsoPeriodic
