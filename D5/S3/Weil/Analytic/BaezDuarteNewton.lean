/- GID: D5/S3/Weil/Analytic/BaezDuarteNewton
   generality: G
   mirror-B: D5/B/S3/Weil/Analytic/BaezDuarteNewton
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual Baez-Duarte Newton series sums to reciprocal zeta on Re(s)>1. -/
import D5.S3.Analytic.SeriesInequalities.NormalizedPochhammerBounds
import D5.S3.Analytic.SeriesInequalities.BaezDuarteQBounds
import D5.S3.Weil.ZetaBridge.RieszBaezDuarte
import Mathlib.Analysis.Analytic.Binomial

open scoped BigOperators
open D5.S3.Analytic.SeriesInequalities.NormalizedPochhammerBounds
open D5.S3.Analytic.SeriesInequalities.BaezDuarteQBounds
open D5.S3.Weil.RieszBaezDuarte

namespace D5.S3.Weil.Analytic.BaezDuarteNewton

private theorem signed_choose (k : ℕ) (z : ℂ) :
    normalizedPochhammer k z = (-1 : ℂ)^k * Ring.choose (z - 1) k := by
  rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval]
  simp only [normalizedPochhammer, descPochhammer_eval_eq_ascPochhammer, smul_eq_mul]
  ring

private theorem binomial_hasSum (z t : ℂ) (ht : ‖t‖ < 1) :
    HasSum (fun k : ℕ => normalizedPochhammer k z * t^k) ((1-t)^(z-1)) := by
  have hm : -t ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa using ht
  have h := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := z-1)).hasSum hm
  have hv (k : ℕ) : (binomialSeries ℂ (z-1) k) (fun _ => -t) =
      normalizedPochhammer k z * t^k := by
    rw [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq]
    rw [smul_eq_mul, signed_choose, neg_pow]
    ring
  have hh := h.congr_fun (fun k => (hv k).symm)
  simpa only [zero_add, sub_eq_add_neg] using hh

private noncomputable def q (n : ℕ) : ℝ := 1 / ((n+1 : ℕ) : ℝ)^2

private theorem q_bounds (n : ℕ) : 0 < q n ∧ q n ≤ 1 := by
  have hn : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  constructor
  · exact one_div_pos.mpr (sq_pos_of_pos (by positivity))
  · exact (div_le_one (by positivity)).mpr (by nlinarith)

private theorem weighted_q_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun k : ℕ => baezDuarteQ k * ‖normalizedPochhammer k (s/2)‖) := by
  let R := ‖s/2‖
  have he : -(1/2 : ℝ) - (s/2).re < -1 := by
    simp only [Complex.div_ofNat_re]
    linarith
  have hsum := (Real.summable_nat_rpow.mpr he).mul_left (3 * Real.exp (R + R^2))
  apply hsum.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (baez_duarte_q_nonneg k) (norm_nonneg _))]
  calc
    _ ≤ (3 * (k : ℝ)^(-(1/2 : ℝ))) *
        (Real.exp (R + R^2) * (k : ℝ)^(-(s/2).re)) :=
      mul_le_mul (baez_duarte_q_le_rpow k hk)
        (normalized_pochhammer_norm_le R (norm_nonneg _) k hk (s/2) le_rfl)
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [sub_eq_add_neg, Real.rpow_add hkpos]; ring

private theorem unsigned_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : ℕ × ℕ =>
      q p.2 * (1-q p.2)^p.1 * ‖normalizedPochhammer p.1 (s/2)‖) := by
  have hnonneg (p : ℕ × ℕ) :
      0 ≤ q p.2 * (1-q p.2)^p.1 * ‖normalizedPochhammer p.1 (s/2)‖ :=
    mul_nonneg (mul_nonneg (q_bounds p.2).1.le
      (pow_nonneg (sub_nonneg.mpr (q_bounds p.2).2) _)) (norm_nonneg _)
  apply (summable_prod_of_nonneg hnonneg).mpr
  constructor
  · intro k
    dsimp only [q]
    exact (baez_duarte_q_summable k).mul_right _
  · have heq (k : ℕ) : (∑' n, q n * (1-q n)^k * ‖normalizedPochhammer k (s/2)‖) =
        baezDuarteQ k * ‖normalizedPochhammer k (s/2)‖ := by
      dsimp only [q, baezDuarteQ]
      exact ((baez_duarte_q_summable k).hasSum.mul_right _).tsum_eq
    simp only [heq]
    exact weighted_q_summable hs

private noncomputable def kernel (s : ℂ) (p : ℕ × ℕ) : ℂ :=
  (((ArithmeticFunction.moebius (p.2+1) : ℝ) / ((p.2+1 : ℕ) : ℝ)^2 *
    (1-q p.2)^p.1 : ℝ) : ℂ) * normalizedPochhammer p.1 (s/2)

private theorem kernel_norm_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : ℕ × ℕ => ‖kernel s p‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (unsigned_summable hs)
  intro p
  have ht : 0 ≤ 1-q p.2 := sub_nonneg.mpr (q_bounds p.2).2
  simp only [kernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_of_nonneg (sq_nonneg ((p.2+1 : ℕ) : ℝ)), abs_of_nonneg (pow_nonneg ht _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg ht _)
  have hm : |(ArithmeticFunction.moebius (p.2+1) : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := p.2+1))
  exact div_le_div_of_nonneg_right hm (sq_nonneg _)

example (z : ℂ) : normalizedPochhammer 0 z = 1 := normalized_pochhammer_zero z
example (z : ℂ) : normalizedPochhammer 1 z = 1-z := by
  simp [normalizedPochhammer]
example (z : ℂ) : HasSum (fun k => normalizedPochhammer k z * (0 : ℂ)^k) 1 := by
  simpa using binomial_hasSum z 0 (by norm_num)

end D5.S3.Weil.Analytic.BaezDuarteNewton
