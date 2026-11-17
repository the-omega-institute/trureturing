/- GID: D5/S3/Arith/Divisors/OeisA130095RatioLimit
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/OeisA130095RatioLimit
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Fibonacci]
   utility: none
   digest: The A130095 successive-term ratio tends to the squared golden ratio. -/

/- admission_basis: open-problem-resolution, preregistered in issue 29484.
   proof_shape: all lemmas and result are bind-only applications and combinations
   of pinned Mathlib results. Every private lemma is consumed on the live path to
   result; none is claimed as a separate research contribution. -/

module

public import Mathlib.Analysis.SpecificLimits.Fibonacci
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Tactic

/-! The complete ratio conjecture for the divisor transform of odd Fibonacci numbers. -/

public section

open Filter Finset
open scoped Topology

namespace D5.S3.Arith.Divisors.OeisA130095RatioLimit

/-- OEIS A130095, using F₀ = 0 and F₁ = 1. The value at zero is the empty sum. -/
def a (n : ℕ) : ℕ := ∑ d ∈ n.divisors, Nat.fib (2 * d - 1)

private def remainder (n : ℕ) : ℕ :=
  ∑ d ∈ n.properDivisors, Nat.fib (2 * d - 1)

private theorem split (n : ℕ) (hn : n ≠ 0) :
    a n = Nat.fib (2 * n - 1) + remainder n := by
  unfold a remainder
  rw [← Nat.cons_self_properDivisors hn, Finset.sum_cons]

private theorem a_pos (n : ℕ) (hn : 1 ≤ n) : 0 < a n := by
  rw [split n (by omega)]
  have : 0 < Nat.fib (2 * n - 1) := Nat.fib_pos.mpr (by omega)
  omega

private theorem remainder_le (n : ℕ) (hn : n ≠ 0) : remainder n ≤ Nat.fib n := by
  have hsub : n.properDivisors ⊆ range (n / 2 + 1) := by
    intro d hd
    rcases (Nat.mem_properDivisors_iff_exists hn).mp hd with ⟨k, hk, hmul⟩
    have : 2 * d ≤ n := by nlinarith
    exact mem_range.mpr (by omega)
  have hsum (m : ℕ) : (∑ d ∈ range (m + 1), Nat.fib (2 * d - 1)) = Nat.fib (2 * m) := by
    have ht := Finset.sum_range_tsub
      (show Monotone (fun j => Nat.fib (2 * j)) from
        fun i j hij => Nat.fib_mono (by omega)) m
    have he (j : ℕ) : Nat.fib (2 * (j + 1)) - Nat.fib (2 * j) = Nat.fib (2 * j + 1) := by
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, Nat.fib_add_two,
        Nat.add_sub_cancel_left]
    simp only [he, Nat.mul_zero, Nat.fib_zero, Nat.sub_zero] at ht
    rw [Finset.sum_range_succ']
    simpa only [show ∀ j : ℕ, 2 * (j + 1) - 1 = 2 * j + 1 by omega,
      Nat.mul_zero, Nat.zero_sub, Nat.fib_zero, Nat.add_zero] using ht
  exact (Finset.sum_le_sum_of_subset hsub).trans
    ((hsum (n / 2)).le.trans (Nat.fib_mono (by omega)))

private theorem fib_square_le (n : ℕ) (hn : 1 ≤ n) :
    Nat.fib n ^ 2 ≤ Nat.fib (2 * n - 1) := by
  have h := Nat.fib_two_mul_add_one (n - 1)
  rw [show 2 * (n - 1) + 1 = 2 * n - 1 by omega,
    Nat.sub_add_cancel hn] at h
  omega

private theorem inverse_fib_limit :
    Tendsto (fun n : ℕ => (1 : ℝ) / Nat.fib n) atTop (nhds 0) := by
  have hf : Tendsto (fun n : ℕ => (Nat.fib n : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 5] with n hn
    exact_mod_cast Nat.le_fib_self hn
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hf

private theorem remainder_ratio_limit :
    Tendsto (fun n : ℕ => (remainder n : ℝ) / Nat.fib (2 * n - 1))
      atTop (nhds 0) := by
  apply squeeze_zero' _ _ inverse_fib_limit
  · exact Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hpos : (0 : ℝ) < Nat.fib n := by exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < n)
    have hopos : (0 : ℝ) < Nat.fib (2 * n - 1) := by
      exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < 2 * n - 1)
    apply (div_le_div_iff₀ hopos hpos).mpr
    have hr : (remainder n : ℝ) ≤ Nat.fib n := by exact_mod_cast remainder_le n (by omega)
    have hs : (Nat.fib n : ℝ) ^ 2 ≤ Nat.fib (2 * n - 1) := by exact_mod_cast fib_square_le n hn
    nlinarith

private theorem odd_ratio_limit :
    Tendsto (fun n : ℕ => (Nat.fib (2 * n - 1) : ℝ) / Nat.fib (2 * (n - 1) - 1))
      atTop (nhds (Real.goldenRatio ^ 2)) := by
  have hk : Tendsto (fun n : ℕ => 2 * n - 3) atTop atTop :=
    (tendsto_sub_atTop_nat 3).comp
      (tendsto_atTop_mono (fun n : ℕ => by omega : ∀ n : ℕ, n ≤ 2 * n) tendsto_id)
  have h₀ := tendsto_fib_succ_div_fib_atTop.comp hk
  have h₁ := tendsto_fib_succ_div_fib_atTop.comp ((tendsto_add_atTop_nat 1).comp hk)
  have hprod := h₁.mul h₀
  rw [← pow_two] at hprod
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hp : (Nat.fib (2 * n - 3 + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < 2 * n - 3 + 1)).ne'
  dsimp
  rw [show 2 * n - 3 + 1 + 1 = 2 * n - 1 by omega,
    show 2 * (n - 1) - 1 = 2 * n - 3 by omega]
  field_simp

private theorem full_ratio_limit :
    Tendsto (fun n : ℕ => (a n : ℝ) / a (n - 1))
      atTop (nhds (Real.goldenRatio ^ 2)) := by
  have he := remainder_ratio_limit.add_const 1
  have hs : Tendsto (fun n : ℕ => n - 1) atTop atTop := tendsto_sub_atTop_nat 1
  have h := odd_ratio_limit.mul (he.div (he.comp hs) (by norm_num : (0 : ℝ) + 1 ≠ 0))
  simp only [zero_add, div_self (by norm_num : (1 : ℝ) ≠ 0), mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : n ≠ 0 := by omega
  have hprev0 : n - 1 ≠ 0 := by omega
  have hfp : (Nat.fib (2 * n - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < 2 * n - 1)).ne'
  have hfm : (Nat.fib (2 * (n - 1) - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < 2 * (n - 1) - 1)).ne'
  have hap : (a (n - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (a_pos (n - 1) (by omega)).ne'
  have hsn : (a n : ℝ) = Nat.fib (2 * n - 1) + remainder n := by exact_mod_cast split n hn0
  have hsm : (a (n - 1) : ℝ) = Nat.fib (2 * (n - 1) - 1) + remainder (n - 1) := by
    exact_mod_cast split (n - 1) hprev0
  dsimp
  rw [hsn, hsm]
  rw [hsm] at hap
  field_simp
  ring

/-- The complete OEIS conjecture, with every eventual index and epsilon explicit. -/
theorem result : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    |(a n : ℝ) / a (n - 1) - ((1 + Real.sqrt 5) / 2) ^ 2| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp full_ratio_limit ε hε
  refine ⟨max N 2, le_max_right _ _, fun n hn => ?_⟩
  simpa only [Real.dist_eq, Real.goldenRatio] using hN n ((le_max_left N 2).trans hn)

end D5.S3.Arith.Divisors.OeisA130095RatioLimit
