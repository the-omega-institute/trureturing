/- GID: D5/S3/PrimeGaps/ModFourChebyshev
   generality: G
   mirror-B: D5/B/S3/PrimeGaps/ModFourChebyshev
   mirror-E: none(waiver:analytic-estimate)
   anchors: [mathlib/module/Mathlib.NumberTheory.LegendreSymbol.ZModChar]
   utility: none
   digest: Weighted residue estimates give a uniform prime-count lower bound. -/

import D5.S3.Weil.Mertens.Estimates
import D5.S3.PrimeGaps.ChiFourWeightedMangoldt
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Tactic

/-!
Classical Dirichlet--Mertens estimates in the residue class one modulo four.
Admission basis: open-problem-resolution; utility: none.
The prime-count estimate is consumed by the Euler-form relative-density proof.

Direct frozen dependencies:
* D5/S3/PrimeGaps/ChiFourWeightedMangoldt.abs_weighted_mangoldt_sum_le_twelve
* D5/S3/Weil/Mertens/Estimates.sum_mangoldt_div_eq_log
* D5/S3/Weil/Mertens/Estimates.E₁Λ.le_E₁p_add_E₁
* D5/S3/Weil/Mertens/Estimates.E₁.le

Declaration proof shapes and live consumers:
* character_bounds: bind-only; residue_gap_bounds.
* residue_prime_identity: bind-only; residue_gap_bounds.
* residue_gap_bounds: bind-only; weighted_mertens.
* prime_window_bound: bind-only; prime_count_lower.
* weighted_mertens: bind-only; prime_count_lower.
* prime_count_lower: bind-only; Euler-form relative density.
The primeCount definition is consumed by prime_window_bound and prime_count_lower.
The private primeWeight definition is consumed by residue_gap_bounds and weighted_mertens.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real Filter
open scoped BigOperators Topology

namespace D5.S3.PrimeGaps.ModFourChebyshev

attribute [local instance] Classical.propDecidable

/-- The number of primes in the residue class one modulo four up to a real bound. -/
def primeCount (x : ℝ) : ℕ :=
  ((Ioc 0 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ p % 4 = 1)).card

private def primeWeight (x : ℝ) : ℝ :=
  ∑ p ∈ (Ioc 0 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ p % 4 = 1), log p / p

private lemma character_bounds (n : ℕ) :
    -1 ≤ (ZMod.χ₄ (n : ZMod 4) : ℝ) ∧
      (ZMod.χ₄ (n : ZMod 4) : ℝ) ≤ 1 := by
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  split_ifs <;> norm_num

private lemma residue_prime_identity {p : ℕ} (hp : p.Prime) :
    log p / p + (ZMod.χ₄ (p : ZMod 4) : ℝ) * log p / p -
      2 * (if p % 4 = 1 then log p / p else 0) =
        if p = 2 then log 2 / 2 else 0 := by
  rcases hp.eq_two_or_odd with rfl | hodd
  · norm_num [ZMod.χ₄]
  · have hne : p ≠ 2 := by omega
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp only [hodd, Nat.one_ne_zero, ite_false, hne]
    split_ifs <;> push_cast <;> ring

private lemma residue_gap_bounds {x : ℝ} (hx : 1 ≤ x) :
    let M := ∑ n ∈ Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / n
    let T := ∑ n ∈ Ioc 0 ⌊x⌋₊,
      (ZMod.χ₄ (n : ZMod 4) : ℝ) * ArithmeticFunction.vonMangoldt n / n
    0 ≤ M + T - 2 * primeWeight x ∧
      M + T - 2 * primeWeight x ≤ 2 * Mertens.E₁ + log 2 / 2 := by
  dsimp only
  let S := Ioc 0 ⌊x⌋₊
  let a (n : ℕ) := ArithmeticFunction.vonMangoldt n / n
  let b (n : ℕ) := if n.Prime then log n / n else 0
  let c (n : ℕ) := if n.Prime ∧ n % 4 = 1 then log n / n else 0
  let g (n : ℕ) :=
    a n + (ZMod.χ₄ (n : ZMod 4) : ℝ) * a n - 2 * c n
  have hg (n : ℕ) : 0 ≤ g n ∧
      g n ≤ 2 * (a n - b n) + if n = 2 then log 2 / 2 else 0 := by
    have ha : 0 ≤ a n := by
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
    by_cases hn : n.Prime
    · have hid : g n = if n = 2 then log 2 / 2 else 0 := by
        dsimp only [g, a, c]
        simp only [hn, true_and, ArithmeticFunction.vonMangoldt_apply_prime hn]
        rw [← mul_div_assoc]
        exact residue_prime_identity hn
      rw [hid]
      constructor
      · split_ifs <;> positivity
      · simp [a, b, hn, ArithmeticFunction.vonMangoldt_apply_prime hn]
    · have hb : b n = 0 := by simp [b, hn]
      have hc : c n = 0 := by simp [c, hn]
      have hlow := mul_le_mul_of_nonneg_right (character_bounds n).1 ha
      have hupp := mul_le_mul_of_nonneg_right (character_bounds n).2 ha
      have hdelta : 0 ≤ (if n = 2 then log 2 / 2 else 0 : ℝ) := by
        split_ifs <;> positivity
      dsimp only [g]
      rw [hb, hc]
      constructor <;> nlinarith
  have hsum : (∑ n ∈ S, g n) =
      (∑ n ∈ S, ArithmeticFunction.vonMangoldt n / n) +
      (∑ n ∈ S,
        (ZMod.χ₄ (n : ZMod 4) : ℝ) * ArithmeticFunction.vonMangoldt n / n) -
      2 * primeWeight x := by
    simp only [g, a, c, mul_div_assoc, sum_sub_distrib, sum_add_distrib,
      ← mul_sum, primeWeight, S, ← sum_filter]
  rw [← hsum]
  refine ⟨sum_nonneg (fun n _ => (hg n).1), ?_⟩
  calc
    _ ≤ ∑ n ∈ S, (2 * (a n - b n) + if n = 2 then log 2 / 2 else 0) :=
      sum_le_sum (fun n _ => (hg n).2)
    _ = 2 * ((∑ n ∈ S, a n) - ∑ n ∈ S, b n) +
        ∑ n ∈ S, if n = 2 then log 2 / 2 else 0 := by
      rw [sum_add_distrib, ← mul_sum, sum_sub_distrib]
    _ ≤ 2 * Mertens.E₁ + log 2 / 2 := by
      have hcor := Mertens.E₁Λ.le_E₁p_add_E₁ hx
      dsimp only [Mertens.E₁Λ, Mertens.E₁p] at hcor
      have hdelta : (∑ n ∈ S, if n = 2 then log 2 / 2 else 0) ≤ log 2 / 2 := by
        rw [Finset.sum_ite_eq']
        split_ifs
        · exact le_rfl
        · positivity
      have hb : (∑ n ∈ S, b n) =
          ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, log n / n := by
        simp only [b, S, ← sum_filter]
      dsimp only [a, S]
      rw [hb]
      linarith

private lemma prime_window_bound {x : ℝ} (hx : exp 50 ≤ x) :
    primeWeight x - primeWeight (x / exp 50) ≤
      (primeCount x : ℝ) * (exp 50 / x * log x) := by
  let S := (Ioc 0 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ p % 4 = 1)
  let U := (Ioc 0 ⌊x / exp 50⌋₊).filter (fun p : ℕ => p.Prime ∧ p % 4 = 1)
  have he : 0 < exp (50 : ℝ) := exp_pos _
  have he1 : 1 ≤ exp (50 : ℝ) := one_le_exp (by norm_num)
  have hx0 : 0 < x := lt_of_lt_of_le he hx
  have hy0 : 0 ≤ x / exp 50 := (div_pos hx0 he).le
  have hyx : x / exp 50 ≤ x := div_le_self hx0.le he1
  have hUS : U ⊆ S := by
    apply filter_subset_filter
    exact Ioc_subset_Ioc le_rfl (Nat.floor_le_floor hyx)
  have hlog : 0 ≤ log x := log_nonneg (le_trans he1 hx)
  have hc : 0 ≤ exp 50 / x * log x := mul_nonneg (div_pos he hx0).le hlog
  have hwindow (p : ℕ) (hp : p ∈ S \ U) :
      log p / p ≤ exp 50 / x * log x := by
    obtain ⟨hpS, hpU⟩ := mem_sdiff.mp hp
    obtain ⟨hpI, hpPrime, hpMod⟩ := mem_filter.mp hpS
    obtain ⟨hp0, hpX⟩ := mem_Ioc.mp hpI
    have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr hp0
    have hpx : (p : ℝ) ≤ x := (Nat.le_floor_iff hx0.le).mp hpX
    have hyp : x / exp 50 < p := by
      have hnle : ¬ p ≤ ⌊x / exp 50⌋₊ := by
        intro h
        exact hpU (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp0, h⟩, hpPrime, hpMod⟩)
      exact (Nat.floor_lt hy0).mp (Nat.lt_of_not_ge hnle)
    have hinv : (p : ℝ)⁻¹ ≤ exp 50 / x := by
      apply (le_div_iff₀ hx0).mpr
      calc
        _ = x / p := by rw [div_eq_mul_inv]; ring
        _ ≤ exp 50 := (div_le_iff₀ hp).mpr (by
          have h := (div_lt_iff₀ he).mp hyp
          nlinarith)
    calc
      _ ≤ log x / p :=
        div_le_div_of_nonneg_right (log_le_log hp hpx) hp.le
      _ = log x * (p : ℝ)⁻¹ := div_eq_mul_inv _ _
      _ ≤ log x * (exp 50 / x) := mul_le_mul_of_nonneg_left hinv hlog
      _ = _ := mul_comm _ _
  calc
    _ = ∑ p ∈ S \ U, log p / p := by
      rw [sum_sdiff_eq_sub hUS]
      rfl
    _ ≤ ∑ _p ∈ S \ U, exp 50 / x * log x :=
      sum_le_sum hwindow
    _ ≤ ∑ _p ∈ S, exp 50 / x * log x :=
      sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => hc)
    _ = _ := by simp [S, primeCount, nsmul_eq_mul]

private lemma weighted_mertens {x : ℝ} (hx : 1 ≤ x) :
    |primeWeight x - (1 / 2 : ℝ) * log x| ≤ 12 := by
  have hM := Mertens.sum_mangoldt_div_eq_log hx
  have hT := ChiFourWeightedMangoldt.abs_weighted_mangoldt_sum_le_twelve hx
  have hgap := residue_gap_bounds hx
  have hlog2 : log 2 ≤ 1 := by
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog4 : log 4 ≤ 2 := by
    have h : log (4 : ℝ) = 2 * log 2 := by
      convert log_pow (2 : ℝ) 2 using 1 <;> norm_num
    linarith
  have hE : Mertens.E₁ ≤ 2 := by linarith [Mertens.E₁.le]
  rw [abs_le] at hM hT ⊢
  dsimp only at hgap
  constructor <;> linarith

/-- A uniform classical lower bound for primes congruent to one modulo four. -/
theorem prime_count_lower {x : ℝ} (hx : exp 50 ≤ x) :
    exp (-50) * x / log x ≤ (primeCount x : ℝ) := by
  have he : 0 < exp (50 : ℝ) := exp_pos _
  have he1 : 1 < exp (50 : ℝ) := one_lt_exp_iff.mpr (by norm_num)
  have hx0 : 0 < x := lt_of_lt_of_le he hx
  have hx1 : 1 < x := lt_of_lt_of_le he1 hx
  have hlog : 0 < log x := log_pos hx1
  have hy1 : 1 ≤ x / exp 50 := (le_div_iff₀ he).mpr (by simpa using hx)
  have hxM := weighted_mertens hx1.le
  have hyM := weighted_mertens hy1
  have hlogy : log (x / exp 50) = log x - 50 := by
    rw [log_div hx0.ne' he.ne', log_exp]
  have hwindow : 1 ≤ primeWeight x - primeWeight (x / exp 50) := by
    rw [abs_le] at hxM hyM
    rw [hlogy] at hyM
    linarith
  have hcount := hwindow.trans (prime_window_bound hx)
  have hprod : x ≤ (primeCount x : ℝ) * exp 50 * log x := by
    have h := (le_div_iff₀ hx0).mp
      (show (1 : ℝ) ≤ ((primeCount x : ℝ) * exp 50 * log x) / x by
        convert hcount using 1 <;> ring)
    simpa using h
  rw [exp_neg, inv_mul_eq_div]
  apply (div_le_iff₀ hlog).mpr
  apply (div_le_iff₀ he).mpr
  nlinarith

end D5.S3.PrimeGaps.ModFourChebyshev
