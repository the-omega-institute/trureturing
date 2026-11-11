/- GID: D5/S3/Arith/Divisors/ProperDivisorPowerBudget
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/ProperDivisorPowerBudget
   mirror-E: none(waiver:symbolic-divisor-estimate)
   anchors: []
   utility: none
   digest: Finite reciprocal-square bounds control every proper-divisor power sum. -/

/- admission_basis: escape-witness. Proposed content: square_budget injects complementary proper divisors into the finite reciprocal-square interval and obtains a full additive n margin. power_budget consumes that estimate; HannaUniformCorrection.exponent_bounds consumes power_budget. utility none: uniform symbolic bounds, no bounded enumeration or numeric reduction. -/


import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace D5.S3.Arith.Divisors.ProperDivisorPowerBudget

open Finset

/-- The complementary-divisor injection gives a finite quadratic budget. -/
theorem square_budget (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.properDivisors, (d : ℚ) ^ 2) + n ≤ (n : ℚ) ^ 2 := by
  classical
  let S := n.divisors.filter (fun k => 1 < k)
  have he : (∑ d ∈ n.properDivisors, (d : ℚ) ^ 2) =
      (n : ℚ) ^ 2 * ∑ k ∈ S, ((k : ℚ) ^ 2)⁻¹ := by
    rw [mul_sum]
    apply sum_bij (fun d _ => n / d)
    · intro d hd
      have hdp := Nat.pos_of_mem_properDivisors hd
      have hdn := (Nat.mem_properDivisors.mp hd).1
      have hdlt := (Nat.mem_properDivisors.mp hd).2
      refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdn, hn.ne'⟩, ?_⟩
      exact Nat.one_lt_div_of_mem_properDivisors hd
    · intro d hd e he h
      exact (Nat.div_eq_iff_eq_of_dvd_dvd hn.ne'
        (Nat.mem_properDivisors.mp hd).1 (Nat.mem_properDivisors.mp he).1).mp h
    · intro k hk
      rcases mem_filter.mp hk with ⟨hkn, hk⟩
      have hkd := Nat.dvd_of_mem_divisors hkn
      refine ⟨n / k, Nat.mem_properDivisors.mpr
        ⟨Nat.div_dvd_of_dvd hkd, Nat.div_lt_self hn hk⟩, ?_⟩
      exact Nat.div_div_self hkd hn.ne'
    · intro d hd
      have hdn := (Nat.mem_properDivisors.mp hd).1
      have hdp := Nat.pos_of_mem_properDivisors hd
      have hqp : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hdp
      have hm : (d : ℚ) * (n / d : ℕ) = n := by
        exact_mod_cast Nat.mul_div_cancel' hdn
      have hq0 : ((n / d : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hqp.ne'
      field_simp
      nlinarith [sq_nonneg ((d : ℚ) * (n / d : ℕ) - n)]
  have hsub : S ⊆ Ioc 1 n := by
    intro k hk
    rcases mem_filter.mp hk with ⟨hk, hk1⟩
    exact mem_Ioc.mpr ⟨hk1, Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hk)⟩
  have hb : (∑ k ∈ S, ((k : ℚ) ^ 2)⁻¹) ≤ 1 - (n : ℚ)⁻¹ := by
    calc
      _ ≤ ∑ k ∈ Ioc 1 n, ((k : ℚ) ^ 2)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => inv_nonneg.mpr (sq_nonneg _))
      _ ≤ _ := by simpa using (sum_Ioc_inv_sq_le_sub (α := ℚ) (by decide : 1 ≠ 0) hn)
  rw [he]
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_left hb (sq_nonneg (n : ℚ))
  have hcancel : (n : ℚ) ^ 2 * (n : ℚ)⁻¹ = n := by
    field_simp
  nlinarith

/-- This stronger-than-properness estimate supplies one full integer unit after
division by `n`, uniformly over every natural exponent at least two. -/
theorem power_budget (s n : ℕ) (hs : 2 ≤ s) (hn : 0 < n) :
    (∑ d ∈ n.properDivisors, (d : ℤ) ^ s) + n ≤ (n : ℤ) ^ s := by
  have hb := square_budget n hn
  have hnQ : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hsum : (∑ d ∈ n.properDivisors, (d : ℚ) ^ s) ≤
      (n : ℚ) ^ (s - 2) * ∑ d ∈ n.properDivisors, (d : ℚ) ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hdQ : (0 : ℚ) ≤ d := Nat.cast_nonneg d
    have hdle : (d : ℚ) ≤ n := by
      exact_mod_cast (Nat.mem_properDivisors.mp hd).2.le
    have he : s = (s - 2) + 2 := by omega
    rw [he, pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hdQ hdle _) (sq_nonneg _)
  have hp : (n : ℚ) ≤ (n : ℚ) ^ (s - 2) * n := by
    have := one_le_pow₀ (n := s - 2) hnQ
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hb (pow_nonneg (by positivity : (0 : ℚ) ≤ n) (s - 2))
  have he : (n : ℚ) ^ (s - 2) * (n : ℚ) ^ 2 = (n : ℚ) ^ s := by
    rw [← pow_add, Nat.sub_add_cancel hs]
  rw [he] at hmul
  have hout : (∑ d ∈ n.properDivisors, (d : ℚ) ^ s) + n ≤ (n : ℚ) ^ s := by
    nlinarith
  exact_mod_cast hout

end D5.S3.Arith.Divisors.ProperDivisorPowerBudget
