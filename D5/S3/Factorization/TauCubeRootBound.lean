/- GID: D5/S3/Factorization/TauCubeRootBound
   generality: G
   mirror-B: D5/B/S3/Factorization/TauCubeRootBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp cubic-root bound for the natural divisor count. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2048

open Finset

namespace D5.S3.Factorization.TauCubeRootBound

/-- The divisor count has a sharp cubic-root bound, attained at 2520. -/
theorem result :
    (∀ j : ℕ, 0 < j →
      (j.divisors.card : ℝ) ≤ 8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
        (j : ℝ) ^ ((1 : ℝ) / 3) ∧
      8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
        (j : ℝ) ^ ((1 : ℝ) / 3) < 4 * (j : ℝ) ^ ((1 : ℝ) / 3)) ∧
    ((2520 : ℕ).divisors.card : ℝ) =
      8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
        (2520 : ℝ) ^ ((1 : ℝ) / 3) := by
  let cost : ℕ → ℚ := fun p =>
    if p = 2 then 8 else if p = 3 then 3 else
    if p = 5 then 8 / 5 else if p = 7 then 8 / 7 else 1
  have cost_ge_one (p : ℕ) : 1 ≤ cost p := by
    dsimp [cost]
    split_ifs <;> norm_num
  have ratio_tail (p k a : ℕ) (hka : k ≤ a)
      (hk : (k + 2) ^ 3 ≤ p * (k + 1) ^ 3) :
      (a + 2) ^ 3 ≤ p * (a + 1) ^ 3 := by
    have hcross : (a + 2) * (k + 1) ≤ (k + 2) * (a + 1) := by nlinarith
    have hpow := Nat.pow_le_pow_left hcross 3
    rw [mul_pow, mul_pow] at hpow
    have hm := Nat.mul_le_mul_right ((a + 1) ^ 3) hk
    have h : (a + 2) ^ 3 * (k + 1) ^ 3 ≤
        (p * (a + 1) ^ 3) * (k + 1) ^ 3 := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hpow.trans hm
    exact Nat.le_of_mul_le_mul_right h (by positivity)
  have power_bound (p k : ℕ) (c : ℚ)
      (hbase : ∀ a ≤ k, (a + 1 : ℚ) ^ 3 ≤ c * (p : ℚ) ^ a)
      (hstep : (k + 2) ^ 3 ≤ p * (k + 1) ^ 3) (a : ℕ) :
      (a + 1 : ℚ) ^ 3 ≤ c * (p : ℚ) ^ a := by
    induction a with
    | zero => exact hbase 0 (Nat.zero_le _)
    | succ a ih =>
      by_cases ha : a < k
      · exact hbase (a + 1) ha
      · have ht : (a + 2 : ℚ) ^ 3 ≤ (p : ℚ) * (a + 1 : ℚ) ^ 3 := by
          exact_mod_cast ratio_tail p k a (by omega) hstep
        calc
          (↑(a + 1) + 1 : ℚ) ^ 3 = (a + 2 : ℚ) ^ 3 := by push_cast; ring
          _ ≤ (p : ℚ) * (a + 1 : ℚ) ^ 3 := ht
          _ ≤ (p : ℚ) * (c * (p : ℚ) ^ a) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
          _ = c * (p : ℚ) ^ (a + 1) := by ring
  have prime_bound (p a : ℕ) (hp : p.Prime) :
      (a + 1 : ℚ) ^ 3 ≤ cost p * (p : ℚ) ^ a := by
    by_cases h2 : p = 2
    · subst p
      apply power_bound 2 3 8 ?_ (by norm_num) a
      intro b hb
      interval_cases b <;> norm_num [cost]
    by_cases h3 : p = 3
    · subst p
      apply power_bound 3 2 3 ?_ (by norm_num) a
      intro b hb
      interval_cases b <;> norm_num [cost]
    by_cases h5 : p = 5
    · subst p
      apply power_bound 5 1 (8 / 5) ?_ (by norm_num) a
      intro b hb
      interval_cases b <;> norm_num [cost]
    by_cases h7 : p = 7
    · subst p
      apply power_bound 7 1 (8 / 7) ?_ (by norm_num) a
      intro b hb
      interval_cases b <;> norm_num [cost]
    have hp11 : 11 ≤ p := by
      by_contra h
      interval_cases p <;> norm_num at * <;> exact absurd hp (by decide)
    simp only [cost, if_neg h2, if_neg h3, if_neg h5, if_neg h7]
    apply power_bound p 0 1 ?_ (by norm_num; omega) a
    intro b hb
    have : b = 0 := by omega
    subst b
    norm_num
  have cube_bound (j : ℕ) (hj : 0 < j) :
      35 * j.divisors.card ^ 3 ≤ 1536 * j := by
    have hjq : (j : ℚ) = ∏ p ∈ j.primeFactors, (p : ℚ) ^ j.factorization p := by
      exact_mod_cast Nat.prod_primeFactors_pow_factorization hj.ne'
    have ht : (j.divisors.card : ℚ) =
        ∏ p ∈ j.primeFactors, (j.factorization p + 1 : ℚ) := by
      exact_mod_cast Nat.card_divisors hj.ne'
    have hc : (∏ p ∈ j.primeFactors, cost p) ≤ (1536 / 35 : ℚ) := by
      have hout : ∀ p, p ∉ ({2, 3, 5, 7} : Finset ℕ) → cost p = 1 := by
        intro p hp
        simp only [mem_insert, mem_singleton, not_or] at hp
        simp [cost, hp]
      have heq : (∏ p ∈ ({2, 3, 5, 7} : Finset ℕ), cost p) =
          ∏ p ∈ j.primeFactors ∪ ({2, 3, 5, 7} : Finset ℕ), cost p :=
        prod_subset subset_union_right (fun p _ hp => hout p hp)
      calc
        _ ≤ ∏ p ∈ j.primeFactors ∪ ({2, 3, 5, 7} : Finset ℕ), cost p :=
          prod_le_prod_of_subset_of_one_le subset_union_left
            (fun p _ => by have h := cost_ge_one p; linarith)
            (fun p _ _ => cost_ge_one p)
        _ = ∏ p ∈ ({2, 3, 5, 7} : Finset ℕ), cost p := heq.symm
        _ = (1536 / 35 : ℚ) := by norm_num [cost]
    have h : (j.divisors.card : ℚ) ^ 3 ≤ (1536 / 35 : ℚ) * j := by
      calc
        _ = ∏ p ∈ j.primeFactors, (j.factorization p + 1 : ℚ) ^ 3 := by
          rw [ht, prod_pow]
        _ ≤ ∏ p ∈ j.primeFactors, cost p * (p : ℚ) ^ j.factorization p :=
          prod_le_prod (fun _ _ => by positivity)
            (fun p hp => prime_bound p _ (Nat.prime_of_mem_primeFactors hp))
        _ = (∏ p ∈ j.primeFactors, cost p) * j := by
          rw [prod_mul_distrib, ← hjq]
        _ ≤ (1536 / 35 : ℚ) * j :=
          mul_le_mul_of_nonneg_right hc (by positivity)
    exact_mod_cast (by nlinarith :
      (35 : ℚ) * (j.divisors.card : ℚ) ^ 3 ≤ 1536 * j)
  have hroot (x : ℝ) (hx : 0 ≤ x) :
      (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
    convert Real.rpow_inv_natCast_pow hx (by decide : (3 : ℕ) ≠ 0) using 1
    norm_num
  have hcostroot : 0 < (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have h2520 : (2520 : ℕ).divisors.card = 48 := by decide
  constructor
  · intro j hj
    have hcube : (35 : ℝ) * (j.divisors.card : ℝ) ^ 3 ≤ 1536 * j := by
      exact_mod_cast cube_bound j hj
    have hjroot : 0 < (j : ℝ) ^ ((1 : ℝ) / 3) := by positivity
    have hcostcube := hroot (3 / 35 : ℝ) (by norm_num)
    have hjcube := hroot (j : ℝ) (by positivity)
    have hfirst : (j.divisors.card : ℝ) ≤
        8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) * (j : ℝ) ^ ((1 : ℝ) / 3) := by
      apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by positivity)
      rw [mul_pow, mul_pow, hcostcube, hjcube]
      nlinarith
    have hstrict : 8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) < 4 := by
      have hx : (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) < 1 / 2 := by
        apply lt_of_pow_lt_pow_left₀ 3 (by norm_num)
        rw [hcostcube]
        norm_num
      linarith
    exact ⟨hfirst, (mul_lt_mul_of_pos_right hstrict hjroot)⟩
  · rw [h2520]
    have hcostcube := hroot (3 / 35 : ℝ) (by norm_num)
    have hjcube := hroot (2520 : ℝ) (by norm_num)
    have hp : 0 < 8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
        (2520 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
    symm
    apply (pow_left_inj₀ hp.le (by norm_num : (0 : ℝ) ≤ 48)
      (by decide : (3 : ℕ) ≠ 0)).mp
    rw [mul_pow, mul_pow, hcostcube, hjcube]
    norm_num

#print axioms result

end D5.S3.Factorization.TauCubeRootBound
