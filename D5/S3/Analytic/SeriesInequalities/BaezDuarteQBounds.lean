/- GID: D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/BaezDuarteQBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original unsigned Baez-Duarte Q admits an all-index half-power bound controlling the actual arithmetic coefficients. -/

import D5.S3.Weil.ZetaBridge.RieszBaezDuarte
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

namespace D5.S3.Analytic.SeriesInequalities.BaezDuarteQBounds

private lemma geometric_weight_bound (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (1-t)^k ≤ 1 / (((k+1 : ℕ) : ℝ)) := by
  have h0 : 0 ≤ 1-t := sub_nonneg.mpr ht1
  have h1 : 1-t ≤ 1 := sub_le_self _ ht
  have hs : ((k+1 : ℕ) : ℝ) * (1-t)^k ≤
      ∑ i ∈ Finset.range (k+1), (1-t)^i := by
    calc
      _ = ∑ _i ∈ Finset.range (k+1), (1-t)^k := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi =>
        pow_le_pow_of_le_one h0 h1 (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hg := geom_sum_mul_neg (1-t) (k+1)
  have hp := pow_nonneg h0 (k+1)
  have hm := mul_le_mul_of_nonneg_right hs ht
  have hk : (0 : ℝ) < ((k+1 : ℕ) : ℝ) := by positivity
  apply (le_div_iff₀ hk).mpr
  nlinarith [show 1 - (1-t) = t by ring]

private lemma reciprocal_square_bounds (n : ℕ) :
    0 ≤ 1 / (((n+1 : ℕ) : ℝ)^2) ∧ 1 / (((n+1 : ℕ) : ℝ)^2) ≤ 1 := by
  have hn : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  constructor
  · positivity
  · exact (div_le_one (by positivity)).mpr (by nlinarith)

private lemma q_term_nonneg (k n : ℕ) :
    0 ≤ (1 / (((n+1 : ℕ) : ℝ)^2)) * (1 - 1 / (((n+1 : ℕ) : ℝ)^2))^k :=
  mul_nonneg (reciprocal_square_bounds n).1
    (pow_nonneg (sub_nonneg.mpr (reciprocal_square_bounds n).2) k)

private lemma finite_q_split_bound (k N M : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.range M, (1 / (((n+1 : ℕ) : ℝ)^2)) *
      (1 - 1 / (((n+1 : ℕ) : ℝ)^2))^k) ≤
      (N : ℝ) / (((k+1 : ℕ) : ℝ)) + 1 / (N : ℝ) := by
  let f : ℕ → ℝ := fun n => (1 / (((n+1 : ℕ) : ℝ)^2)) *
    (1 - 1 / (((n+1 : ℕ) : ℝ)^2))^k
  have hp (L : ℕ) : ∑ n ∈ Finset.range L, f n ≤
      (L : ℝ) / (((k+1 : ℕ) : ℝ)) := by
    calc
      _ ≤ ∑ _n ∈ Finset.range L, 1 / (((k+1 : ℕ) : ℝ)) :=
        Finset.sum_le_sum fun n _ => geometric_weight_bound k _
          (reciprocal_square_bounds n).1 (reciprocal_square_bounds n).2
      _ = _ := by simp [div_eq_mul_inv]
  change (∑ n ∈ Finset.range M, f n) ≤ _
  by_cases hNM : N ≤ M
  · have ht : (∑ n ∈ Finset.Ico N M, f n) ≤ 1 / (N : ℝ) := by
      calc
        _ ≤ ∑ n ∈ Finset.Ico N M, 1 / (((n+1 : ℕ) : ℝ)^2) := by
          apply Finset.sum_le_sum
          intro n _
          exact mul_le_of_le_one_right (reciprocal_square_bounds n).1
            (pow_le_one₀ (sub_nonneg.mpr (reciprocal_square_bounds n).2)
              (sub_le_self _ (reciprocal_square_bounds n).1))
        _ = ∑ n ∈ Finset.Ioc N M, ((n : ℝ)^2)⁻¹ := by
          simp only [one_div]
          rw [Finset.sum_Ico_add' (fun n : ℕ => ((n : ℝ)^2)⁻¹) N M 1,
            Finset.Ico_add_one_right_eq_Icc, Finset.Icc_add_one_left_eq_Ioc]
        _ ≤ (N : ℝ)⁻¹ - (M : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub (by omega) hNM
        _ ≤ _ := by simp [one_div]
    rw [← Finset.sum_range_add_sum_Ico f hNM]
    exact add_le_add (hp N) ht
  · calc
      _ ≤ (M : ℝ) / (((k+1 : ℕ) : ℝ)) := hp M
      _ ≤ (N : ℝ) / (((k+1 : ℕ) : ℝ)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast (show M ≤ N by omega)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)

noncomputable def baezDuarteQ (k : ℕ) : ℝ := ∑' n : ℕ,
  (1 / (((n+1 : ℕ) : ℝ)^2)) * (1 - 1 / (((n+1 : ℕ) : ℝ)^2))^k

theorem baez_duarte_q_summable (k : ℕ) : Summable (fun n : ℕ =>
    (1 / (((n+1 : ℕ) : ℝ)^2)) * (1 - 1 / (((n+1 : ℕ) : ℝ)^2))^k) :=
  summable_of_sum_range_le (q_term_nonneg k) (fun M => finite_q_split_bound k 1 M le_rfl)

theorem baez_duarte_q_nonneg (k : ℕ) : 0 ≤ baezDuarteQ k :=
  tsum_nonneg (q_term_nonneg k)

theorem baez_duarte_q_le_three_div_sqrt (k : ℕ) :
    baezDuarteQ k ≤ 3 / Real.sqrt (((k+1 : ℕ) : ℝ)) := by
  let N := Nat.sqrt (k+1)
  have hN : 1 ≤ N := Nat.sqrt_pos.mpr (by omega)
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hK : (0 : ℝ) < ((k+1 : ℕ) : ℝ) := by positivity
  have hr : 0 < Real.sqrt (((k+1 : ℕ) : ℝ)) := Real.sqrt_pos.mpr hK
  have hs := Real.sq_sqrt hK.le
  have hlow : (N : ℝ)^2 ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast Nat.sqrt_le' (k+1)
  have hupp : ((k+1 : ℕ) : ℝ) ≤ ((N : ℝ)+1)^2 := by
    exact_mod_cast (Nat.lt_succ_sqrt' (k+1)).le
  have hNrle : (N : ℝ) ≤ Real.sqrt (((k+1 : ℕ) : ℝ)) := by nlinarith
  have hrN : Real.sqrt (((k+1 : ℕ) : ℝ)) ≤ 2*(N : ℝ) := by nlinarith
  have hsplit : baezDuarteQ k ≤ (N : ℝ) / (((k+1 : ℕ) : ℝ)) + 1/(N : ℝ) :=
    Real.tsum_le_of_sum_range_le (q_term_nonneg k) (fun M => finite_q_split_bound k N M hN)
  calc
    _ ≤ _ := hsplit
    _ ≤ Real.sqrt (((k+1 : ℕ) : ℝ)) / (((k+1 : ℕ) : ℝ)) +
        2 / Real.sqrt (((k+1 : ℕ) : ℝ)) := by
      apply add_le_add (div_le_div_of_nonneg_right hNrle hK.le)
      apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < N) hr).mpr
      simpa using hrN
    _ = _ := by rw [Real.sqrt_div_self']; ring

theorem abs_baez_duarte_le_q (k : ℕ) :
    |D5.S3.Weil.RieszBaezDuarte.baezDuarte k| ≤ baezDuarteQ k := by
  apply (D5.S3.Weil.RieszBaezDuarte.baez_duarte_hasSum_moebius k).norm_le_of_bounded
    (baez_duarte_q_summable k).hasSum
  intro n
  have hm : |(ArithmeticFunction.moebius (n+1) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n+1)
  have hn := reciprocal_square_bounds n
  calc
    _ = |(ArithmeticFunction.moebius (n+1) : ℝ)| *
        ((1 / (((n+1 : ℕ) : ℝ)^2)) * (1-1/(((n+1 : ℕ) : ℝ)^2))^k) := by
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow,
        abs_of_nonneg (show (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) by positivity),
        abs_of_nonneg (pow_nonneg (sub_nonneg.mpr hn.2) k)]
      ring
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hm (q_term_nonneg k n)

theorem abs_baez_duarte_le_three_div_sqrt (k : ℕ) :
    |D5.S3.Weil.RieszBaezDuarte.baezDuarte k| ≤
      3 / Real.sqrt (((k+1 : ℕ) : ℝ)) :=
  (abs_baez_duarte_le_q k).trans (baez_duarte_q_le_three_div_sqrt k)

theorem baez_duarte_q_le_rpow (k : ℕ) (hk : 1 ≤ k) :
    baezDuarteQ k ≤ 3 * Real.rpow (k : ℝ) (-(1/2 : ℝ)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  calc
    _ ≤ 3 / Real.sqrt (((k+1 : ℕ) : ℝ)) := baez_duarte_q_le_three_div_sqrt k
    _ ≤ 3 / Real.sqrt (k : ℝ) := by
      apply div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hk0)
      exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k)
    _ = _ := by
      change 3 / Real.sqrt (k : ℝ) = 3 * (k : ℝ)^(-(1/2 : ℝ))
      rw [Real.rpow_neg hk0.le, ← Real.sqrt_eq_rpow]; rfl

theorem abs_baez_duarte_le_rpow (k : ℕ) (hk : 1 ≤ k) :
    |D5.S3.Weil.RieszBaezDuarte.baezDuarte k| ≤
      3 * Real.rpow (k : ℝ) (-(1/2 : ℝ)) :=
  (abs_baez_duarte_le_q k).trans (baez_duarte_q_le_rpow k hk)

theorem baez_duarte_q_zero_le_two : baezDuarteQ 0 ≤ 2 := by
  have h := Real.tsum_le_of_sum_range_le (q_term_nonneg 0)
    (fun M => finite_q_split_bound 0 1 M le_rfl)
  convert h using 1 <;> norm_num [baezDuarteQ]

-- Full-domain checks: endpoints, empty and nonempty prefixes, and the original first term.
example (k : ℕ) : (0 : ℝ) * (1-0)^k ≤ 1 / (((k+1 : ℕ) : ℝ)) :=
  geometric_weight_bound k 0 le_rfl zero_le_one
example (k : ℕ) : (1 : ℝ) * (1-1)^k ≤ 1 / (((k+1 : ℕ) : ℝ)) :=
  geometric_weight_bound k 1 zero_le_one le_rfl
example (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : t * (1-t)^0 ≤ 1 := by
  simpa using geometric_weight_bound 0 t h0 h1
example (k M : ℕ) : (∑ n ∈ Finset.range M, (1 / (((n+1 : ℕ) : ℝ)^2)) *
    (1 - 1 / (((n+1 : ℕ) : ℝ)^2))^k) ≤ 1 / (((k+1 : ℕ) : ℝ)) + 1 := by
  simpa using finite_q_split_bound k 1 M le_rfl
example (k : ℕ) : (∑ n ∈ Finset.range 0, (1 / (((n+1 : ℕ) : ℝ)^2)) *
    (1 - 1 / (((n+1 : ℕ) : ℝ)^2))^k) ≤ 1 / (((k+1 : ℕ) : ℝ)) + 1 := by
  simpa using finite_q_split_bound k 1 0 le_rfl
example (k : ℕ) : (∑ n ∈ Finset.range 1, (1 / (((n+1 : ℕ) : ℝ)^2)) *
    (1 - 1 / (((n+1 : ℕ) : ℝ)^2))^k) ≤ 1 / (((k+1 : ℕ) : ℝ)) + 1 := by
  simpa using finite_q_split_bound k 1 1 le_rfl
example (k : ℕ) : (∑ n ∈ Finset.range 2, (1 / (((n+1 : ℕ) : ℝ)^2)) *
    (1 - 1 / (((n+1 : ℕ) : ℝ)^2))^k) ≤ 1 / (((k+1 : ℕ) : ℝ)) + 1 := by
  simpa using finite_q_split_bound k 1 2 le_rfl
example : (1 / (((0+1 : ℕ) : ℝ)^2)) * (1-1/(((0+1 : ℕ) : ℝ)^2))^0 = 1 := by
  norm_num
example (k : ℕ) : (1 / (((0+1 : ℕ) : ℝ)^2)) * (1-1/(((0+1 : ℕ) : ℝ)^2))^(k+1) = 0 := by
  norm_num
example : 1 ≤ baezDuarteQ 0 := by
  have h := (baez_duarte_q_summable 0).le_tsum 0 (fun n _ => q_term_nonneg 0 n)
  simpa only [baezDuarteQ, Nat.zero_add, Nat.cast_one, one_pow, div_one, sub_self, pow_zero,
    mul_one] using h
example : |D5.S3.Weil.RieszBaezDuarte.baezDuarte 0| ≤ 2 :=
  (abs_baez_duarte_le_q 0).trans baez_duarte_q_zero_le_two

set_option pp.universes true in
#print baezDuarteQ
#check baezDuarteQ
#print axioms baezDuarteQ
#check geometric_weight_bound
#print axioms geometric_weight_bound
#check reciprocal_square_bounds
#print axioms reciprocal_square_bounds
#check q_term_nonneg
#print axioms q_term_nonneg
#check finite_q_split_bound
#print axioms finite_q_split_bound
#check baez_duarte_q_summable
#print axioms baez_duarte_q_summable
#check baez_duarte_q_nonneg
#print axioms baez_duarte_q_nonneg
#check baez_duarte_q_le_three_div_sqrt
#print axioms baez_duarte_q_le_three_div_sqrt
#check abs_baez_duarte_le_q
#print axioms abs_baez_duarte_le_q
#check abs_baez_duarte_le_three_div_sqrt
#print axioms abs_baez_duarte_le_three_div_sqrt
#check baez_duarte_q_le_rpow
#print axioms baez_duarte_q_le_rpow
#check abs_baez_duarte_le_rpow
#print axioms abs_baez_duarte_le_rpow
#check baez_duarte_q_zero_le_two
#print axioms baez_duarte_q_zero_le_two

end D5.S3.Analytic.SeriesInequalities.BaezDuarteQBounds
