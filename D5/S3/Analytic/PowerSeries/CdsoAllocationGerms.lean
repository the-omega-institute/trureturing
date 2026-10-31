/- GID: D5/S3/Analytic/PowerSeries/CdsoAllocationGerms
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual analytic allocation germs and their quadratic Taylor cutoff. -/

import D5.S3.Analytic.PowerSeries.RadicalMultiplicity
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.Polynomial
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
      taylor_add (AnalyticOnNhd.eval_polynomial p 0 (Set.mem_univ 0))
        (AnalyticOnNhd.eval_polynomial q 0 (Set.mem_univ 0))
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


/-- Source branch, residue remainders, and an integer allocation vector.
The analytic conclusions also apply to vectors outside the allocation inequalities. -/
structure AllocationData (a h : ℕ) where
  j : ℕ
  j_pos : 0 < j
  j_le : j ≤ h
  d : ℕ
  d_lt : d < a + j - 1
  t : ℕ
  t_lt : t < h + 1 - j
  z : Fin (a + j) → ℤ

namespace AllocationData

variable {a h : ℕ}

def m (b : AllocationData a h) : ℕ := a + b.j
def r (b : AllocationData a h) : ℕ := b.m - 1
def n (b : AllocationData a h) : ℕ := h + 1 - b.j
def alpha (b : AllocationData a h) : ℝ := ((a : ℝ) - 1) / b.r
def beta (b : AllocationData a h) : ℝ := (b.j : ℝ) / ((b.r : ℝ) * b.n)
def phi (b : AllocationData a h) : ℝ :=
  -((b.n : ℝ) + ((b.r : ℝ) - 1) * b.d) / b.r
def sigma (b : AllocationData a h) : ℝ := ((b.d : ℝ) - b.n) / b.r
def gamma (b : AllocationData a h) : ℝ := ((b.n : ℝ) - b.d) / ((b.r : ℝ) * b.n)
def vminus (b : AllocationData a h) : ℝ := b.gamma - (b.t : ℝ) / b.n
def vplus (b : AllocationData a h) : ℝ := b.vminus + 1

def zplus (b : AllocationData a h) (i : Fin (a + b.j)) : ℝ := max (b.z i : ℝ) 0
def zminus (b : AllocationData a h) (i : Fin (a + b.j)) : ℝ := max (-(b.z i : ℝ)) 0
def L (b : AllocationData a h) : ℝ := b.n - ∑ i, b.zplus i

def zmin (b : AllocationData a h) : ℤ := by
  letI : Nonempty (Fin (a + b.j)) := ⟨⟨0, by have := b.j_pos; omega⟩⟩
  exact Finset.univ.inf' Finset.univ_nonempty b.z

def delta (b : AllocationData a h) (i : Fin (a + b.j)) : ℝ := b.sigma + b.z i
def delta0 (b : AllocationData a h) : ℝ := b.sigma + b.zmin

/-- The source allocation inequalities. They are not separation hypotheses. -/
def Admissible (b : AllocationData a h) : Prop :=
  (∑ i, b.z i) = (b.n : ℤ) - b.d ∧
    (∑ i, max (b.z i) 0) ≤ b.n ∧ (∑ i, max (-b.z i) 0) ≤ b.d

private theorem alpha_pos (b : AllocationData a h) (ha : 2 ≤ a) : 0 < b.alpha := by
  have hr : 0 < b.r := by unfold r m; have := b.j_pos; omega
  unfold alpha
  positivity

private theorem beta_pos (b : AllocationData a h) (ha : 2 ≤ a) : 0 < b.beta := by
  have hr : 0 < b.r := by unfold r m; have := b.j_pos; omega
  have hn : 0 < b.n := by unfold n; have := b.j_le; omega
  unfold beta
  have := b.j_pos
  positivity

/-- The full bracket in source formula (8.4), parametrized by its radical function. -/
def combination (H : ℝ → ℝ → ℝ → ℝ → ℝ) (b : AllocationData a h) (u : ℝ) : ℝ :=
  (∑ i, ((b.alpha + b.phi * u) * H b.alpha (b.delta i) b.m u +
    u * ((b.d : ℝ) - b.zminus i) * H b.alpha (b.delta i) b.r u +
    u * b.zplus i * H b.alpha (b.delta i) 2 u)) +
  u * b.L * (H b.alpha b.delta0 2 u - H b.alpha b.delta0 b.r u) +
  ((b.n : ℝ) - b.t) * ((b.beta + (b.vminus - 1) * u) * H b.beta b.vminus 1 u +
    u * H b.beta b.vminus 2 u) +
  (b.t : ℝ) * ((b.beta + (b.vplus - 1) * u) * H b.beta b.vplus 1 u +
    u * H b.beta b.vplus 2 u)

/-- The actual positive-parameter function in (8.4). -/
def actual (b : AllocationData a h) (u : ℝ) : ℝ :=
  2 / u ^ 2 * b.combination radicalR u

/-- Its removable analytic extension at zero. -/
def extension (b : AllocationData a h) (u : ℝ) : ℝ :=
  2 * b.combination radicalExtension u

private theorem analytic_extension (b : AllocationData a h) (ha : 2 ≤ a) :
    AnalyticAt ℝ b.extension 0 := by
  have hα := b.alpha_pos ha
  have hβ := b.beta_pos ha
  have hcore (i : Fin (a + b.j)) (k : ℝ) :=
    analytic_radicalExtension b.alpha (b.delta i) k hα
  have hmin (k : ℝ) := analytic_radicalExtension b.alpha b.delta0 k hα
  have hminus (k : ℝ) := analytic_radicalExtension b.beta b.vminus k hβ
  have hplus (k : ℝ) := analytic_radicalExtension b.beta b.vplus k hβ
  unfold extension combination
  fun_prop

end AllocationData

end CdsoPeriodic
