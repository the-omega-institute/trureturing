/- GID: D5/S3/Analytic/EllipticTailExponent/Tail
   generality: G
   mirror-B: D5/B/S3/Analytic/EllipticTailExponent/Tail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd, mathlib/module/Mathlib.Topology.Algebra.InfiniteSum.ENNReal]
   utility: none
   digest: The elliptic remainder is a positive coefficient tail through Euler's sine product. -/

import D5.S3.Analytic.EllipticTailExponent.Defs
import D5.S3.Analytic.GaussZeroBalanced.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open Finset Filter
open scoped BigOperators Topology

namespace D5.S3.Analytic.EllipticTailExponent.Tail
open D5.S3.Analytic.EllipticTailExponent.Defs

/-- The normalized pair of ascending products. -/
noncomputable def d (k : ℕ) (a : ℝ) : ℝ :=
  (∏ j ∈ range k, (a + j)) * (∏ j ∈ range k, (1 - a + j)) /
    (Nat.factorial k : ℝ) ^ 2

/-- The summand of the elliptic truncation. -/
noncomputable def t (k : ℕ) (a : ℝ) : ℝ := a * d k a / (k + 1)

private lemma d_eq_coefficient (k : ℕ) (a : ℝ) :
    d k a = ordinaryHypergeometricCoefficient a (1 - a) 1 k := by
  have hp (x : ℝ) : (ascPochhammer ℝ k).eval x = ∏ j ∈ range k, (x + j) := by
    have he := ascPochhammer_eval_neg_eq_descPochhammer ℝ (-x) k
    rw [neg_neg, descPochhammer_eval_eq_prod_range] at he
    rw [he, show (-1 : ℝ) ^ k = ∏ _j ∈ range k, (-1 : ℝ) by simp,
      ← prod_mul_distrib]
    apply prod_congr rfl
    intro j _
    ring
  simp only [d, ordinaryHypergeometricCoefficient, ascPochhammer_eval_one]
  rw [hp a, hp (1 - a)]
  ring

private lemma d_succ (k : ℕ) (a : ℝ) :
    d (k + 1) a = d k a * (a + k) * (1 - a + k) / (k + 1) ^ 2 := by
  have h := D5.S3.Analytic.GaussZeroBalanced.Series.coefficient_recurrence
    (a := a) (b := 1 - a) (c := 1) zero_lt_one k
  rw [← d_eq_coefficient, ← d_eq_coefficient] at h
  apply (eq_div_iff (by positivity : ((k : ℝ) + 1) ^ 2 ≠ 0)).2
  simpa only [Nat.cast_add, Nat.cast_one, pow_two, mul_comm, mul_left_comm,
    mul_assoc, add_comm] using h

private lemma d_step (k : ℕ) (a : ℝ) :
    (k + 1 : ℝ) * d (k + 1) a - k * d k a = (1 - a) * t k a := by
  rw [d_succ, t]
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The weighted coefficient is a finite Euler product. -/
theorem d_product (N : ℕ) (a : ℝ) :
    (N + 1 : ℝ) * d (N + 1) a =
      a * (1 - a / (N + 1)) * ∏ j ∈ range N, (1 - a ^ 2 / ((j : ℝ) + 1) ^ 2) := by
  induction N with
  | zero => simp [d]
  | succ N ih =>
    have hN : (N : ℝ) + 1 ≠ 0 := by positivity
    have hN2 : (N : ℝ) + 2 ≠ 0 := by positivity
    have hd : d (N + 1) a =
        (a * (1 - a / (N + 1)) * ∏ j ∈ range N,
          (1 - a ^ 2 / ((j : ℝ) + 1) ^ 2)) / (N + 1) := by
      apply (eq_div_iff hN).2
      simpa [mul_comm] using ih
    rw [show N + 1 + 1 = (N + 1) + 1 by omega, d_succ, hd, prod_range_succ]
    push_cast
    field_simp
    ring


private lemma sum_t (m : ℕ) (a : ℝ) (ha : a ≠ 1) :
    ∑ k ∈ range m, t k a = m * d m a / (1 - a) := by
  have ha1 : 1 - a ≠ 0 := sub_ne_zero.mpr ha.symm
  apply (eq_div_iff ha1).2
  have hs := sum_range_sub (fun k : ℕ => (k : ℝ) * d k a) m
  simp only [Nat.cast_add, Nat.cast_one, d_step, Nat.cast_zero, zero_mul, sub_zero] at hs
  simpa only [mul_sum, mul_comm] using hs

private lemma t_eq_g6 (k : ℕ) (a : ℝ) :
    t k a = g6 k a / ((k + 1 : ℝ) * (Nat.factorial k : ℝ) ^ 2) := by
  simp only [t, d, g6]
  field_simp

private lemma S_eq_sum_t (n : ℕ) (a : ℝ) :
    S n a = ∑ k ∈ range (n + 1), t k a := by
  simp only [S, t_eq_g6]

private lemma t_nonneg (k : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 2) :
    0 ≤ t k a := by
  unfold t
  rw [d_eq_coefficient]
  exact div_nonneg (mul_nonneg ha.le
    (D5.S3.Analytic.GaussZeroBalanced.Series.coefficient_pos ha
      (by linarith : 0 < 1 - a) zero_lt_one k).le) (by positivity)

private lemma tendsto_weighted_d (a : ℝ) :
    Tendsto (fun N : ℕ => (N + 1 : ℝ) * d (N + 1) a) atTop
      (𝓝 (Real.sin (Real.pi * a) / Real.pi)) := by
  have he := (Real.tendsto_euler_sin_prod a).div_const Real.pi
  have he' : Tendsto (fun N : ℕ => a * ∏ j ∈ range N,
      (1 - a ^ 2 / ((j : ℝ) + 1) ^ 2)) atTop
      (𝓝 (Real.sin (Real.pi * a) / Real.pi)) := by
    convert he using 1
    ext N
    field_simp
  have hz : Tendsto (fun N : ℕ => 1 - a / ((N : ℝ) + 1)) atTop (𝓝 1) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul a)
  convert hz.mul he' using 1
  · ext N
    rw [d_product]
    ring
  · ring

private lemma hasSum_t {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 2) :
    HasSum (fun k => t k a) (Real.sin (Real.pi * a) / (Real.pi * (1 - a))) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => t_nonneg k ha ha1) _).2
  have he := (tendsto_weighted_d a).div_const (1 - a)
  have he' : Tendsto (fun N : ℕ => ∑ k ∈ range (N + 1), t k a) atTop
      (𝓝 (Real.sin (Real.pi * a) / (Real.pi * (1 - a)))) := by
    simpa only [sum_t _ _ (by linarith : a ≠ 1), div_div, Nat.cast_add, Nat.cast_one] using he
  exact (tendsto_add_atTop_iff_nat 1).1 he'

/-- The analytic remainder equals the tail after index n. -/
theorem tail_eq_tsum (n : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 2) :
    Real.sin (Real.pi * a) / (Real.pi * (1 - a)) - S n a =
      ∑' k, t (k + n + 1) a := by
  have hs := ((hasSum_nat_add_iff' (n + 1)).2 (hasSum_t ha ha1)).tsum_eq
  simpa only [← Nat.add_assoc, ← S_eq_sum_t] using hs.symm

end D5.S3.Analytic.EllipticTailExponent.Tail
