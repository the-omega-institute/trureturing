/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripTaylor
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Extended Taylor remainder for the continued left-strip marginal. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MarginalTaylor

/-! A uniform marginal remainder bound for the larger left-strip arguments. -/

open MeasureTheory Set

noncomputable section

namespace RefinedBMV.PositiveCenter.SmallCorner

open DimThree (gaps)

open private Gap exponent denominator denominator_pos exponent_abs_le sum_marginal_square
  marginalTaylorPolynomial_eq_sum from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MarginalTaylor
open private abs_sum_map_sub_le from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.JointTaylor

private def scalarPolynomial (b t : ℝ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, b ^ (k + i) * t ^ i /
    ((i.factorial : ℝ) * (((k + i : ℕ) : ℝ) + 1) * (((k + i : ℕ) : ℝ) + 2))

private theorem weighted_error {b t : ℝ} (hb : |b| ≤ 2) (ht : |t| ≤ 2)
    {k n : ℕ} (hk : k ≤ 2) (hn : n + k = 23) :
    |(∫ s in (0 : ℝ)..1, (1 - s) * (b * s) ^ k * Real.exp (t * (b * s))) -
        scalarPolynomial b t k n| ≤ (2 : ℝ) ^ (k + 1) * 4 ^ n / (n.factorial * 24 * 25) := by
  let w (s : ℝ) := (1 - s) * (b * s) ^ k
  let z (s : ℝ) := t * (b * s)
  let pol (s : ℝ) := ∑ i ∈ Finset.range n, z s ^ i / (i.factorial : ℝ)
  have hpol : (∫ s in (0 : ℝ)..1, w s * pol s) = scalarPolynomial b t k n := by
    simp only [pol, scalarPolynomial, Finset.mul_sum]
    refine (intervalIntegral.integral_finsetSum (fun i _ ↦ ?_)).trans ?_
    · apply Continuous.intervalIntegrable
      dsimp only [w, z]
      fun_prop
    apply Finset.sum_congr rfl
    intro i _
    have heq (s : ℝ) :
        w s * (z s ^ i / (i.factorial : ℝ)) =
          (b ^ (k + i) * t ^ i / (i.factorial : ℝ)) * ((1 - s) * s ^ (k + i)) := by
      simp only [w, z, mul_pow, pow_add]
      ring
    simp_rw [heq]
    rw [intervalIntegral.integral_const_mul, unit_weight_moment]
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev, mul_assoc]
    ac_rfl
  have hv : Continuous (fun s ↦ w s * Real.exp (z s)) := by
    dsimp only [w, z]
    fun_prop
  have hP : Continuous (fun s ↦ w s * pol s) := by
    dsimp only [w, pol, z]
    fun_prop
  let C : ℝ := (2 : ℝ) ^ (k + 1) * 4 ^ n / n.factorial
  have hC : Continuous (fun s : ℝ ↦ C * ((1 - s) * s ^ (n + k))) := by fun_prop
  have hbound (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
      ‖w s * Real.exp (z s) - w s * pol s‖ ≤ C * ((1 - s) * s ^ (n + k)) := by
    have hs₀ : 0 ≤ s := hs.1.le
    have hbs : |b * s| ≤ 2 * s := by
      rw [abs_mul, abs_of_nonneg hs₀]
      exact mul_le_mul_of_nonneg_right hb hs₀
    have hz : |z s| ≤ 4 * s := by
      rw [show z s = t * (b * s) from rfl, abs_mul]
      calc
        _ ≤ 2 * (2 * s) := mul_le_mul ht hbs (abs_nonneg _) (by norm_num)
        _ = _ := by ring
    have hratio : ‖(z s : ℂ)‖ / (n.succ : ℝ) ≤ 1 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, Nat.cast_succ]
      have hnR : (21 : ℝ) ≤ n := by exact_mod_cast (show 21 ≤ n by omega)
      exact (div_le_iff₀ (by positivity)).2 (by linarith [hs.2])
    have htail : |Real.exp (z s) - pol s| ≤ |z s| ^ n / (n.factorial : ℝ) * 2 := by
      dsimp only [pol]
      exact_mod_cast Complex.exp_bound' hratio
    have htail' : |Real.exp (z s) - pol s| ≤ (4 * s) ^ n / (n.factorial : ℝ) * 2 :=
      htail.trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hz _) (by positivity))
        (by norm_num))
    rw [← mul_sub, Real.norm_eq_abs, abs_mul]
    dsimp only [w]
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hs.2), abs_pow, mul_assoc]
    calc
      _ ≤ (1 - s) * ((2 * s) ^ k * ((4 * s) ^ n / (n.factorial : ℝ) * 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hbs _) htail' (abs_nonneg _) (by positivity))
          (sub_nonneg.mpr hs.2)
      _ = _ := by simp only [C, mul_pow, pow_add, pow_one]; ring
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) zero_le_one
    (Filter.Eventually.of_forall hbound) (hC.intervalIntegrable 0 1)
  change |(∫ s in (0 : ℝ)..1, w s * Real.exp (z s)) - scalarPolynomial b t k n| ≤ _
  rw [← hpol, ← intervalIntegral.integral_sub (μ := volume) (hv.intervalIntegrable 0 1)
    (hP.intervalIntegrable 0 1)]
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, unit_weight_moment, hn] at h
  refine h.trans_eq ?_
  norm_num [C, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Uniform absolute error of the degree-`22 - k` Taylor polynomial of the
compact marginal derivative on `[-2, 2]`. -/
private theorem integralMarginalDerivative_sub_taylor_le_two {p k : ℕ} (hp : 0 < p) (hk : k ≤ 2)
    {t : ℝ} (ht : |t| ≤ 2) :
    |integralMarginalDerivative p (compositionMarginalVariance p / 2) k t - marginalTaylorPolynomial p k t| ≤
      (2 : ℝ) ^ (k + 2) * 4 ^ (23 - k) / ((Nat.factorial (23 - k) : ℝ) * 24 * 25) := by
  let n := 23 - k
  let ε : ℝ := (2 : ℝ) ^ (k + 1) * 4 ^ n / (n.factorial * 24 * 25)
  rw [marginalTaylorPolynomial_eq_sum]
  let f (g : Gap) := exponent p g.2.2 ^ 2 *
    (∫ s in (0 : ℝ)..1, (1 - s) * (exponent p g.2.2 * s) ^ k *
      Real.exp (t * (exponent p g.2.2 * s)))
  let pol (g : Gap) := exponent p g.2.2 ^ 2 * scalarPolynomial (exponent p g.2.2) t k n
  let weight (g : Gap) := exponent p g.2.2 ^ 2 * ε
  change |((gaps p).map f).sum / denominator p - ((gaps p).map pol).sum / denominator p| ≤ _
  have hden := denominator_pos p
  have hlocal (g : Gap) (hg : g ∈ gaps p) : |f g - pol g| ≤ weight g := by
    dsimp only [f, pol, weight]
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (weighted_error (exponent_abs_le hp hg) ht hk (n := n) (by dsimp only [n]; omega))
      (sq_nonneg _)
  rw [← sub_div, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  refine (abs_sum_map_sub_le (gaps p) f pol weight hlocal).trans_eq ?_
  dsimp only [weight]
  rw [List.sum_map_mul_right, sum_marginal_square]
  simp only [ε, n, show k + 2 = (k + 1) + 1 by omega, pow_succ]
  ring

end RefinedBMV.PositiveCenter.SmallCorner
