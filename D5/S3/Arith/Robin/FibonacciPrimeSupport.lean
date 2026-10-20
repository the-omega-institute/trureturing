/- GID: D5/S3/Arith/Robin/FibonacciPrimeSupport
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/FibonacciPrimeSupport
   mirror-E: none(waiver:universal-inequality)
   anchors: []
   utility: none
   digest: Integers built from Fibonacci primes have sigma(n)/n below 241/50 and satisfy Robin. -/

import D5.S3.Arith.Robin.FewDistinctPrimes
import Mathlib.Data.Nat.Fib.Basic

/-! A prime Fibonacci number is `2`, `3`, `5` or `F_k` with `k ≥ 7`. For `k ≥ 7` the growth
`2 (F_{k+1} - 1) ≥ 3 (F_k - 1)` telescopes the reciprocals `1 / (F_k - 1)` to at most `1/4`, so
`∏ p/(p-1)` over any set of prime Fibonacci numbers is below `15/4 · e^{1/4} < 241/50`. Robin's
capacity `e^γ log log n` exceeds this from `n = 2^24`, and the frozen eight-prime theorem covers
every `n` below `223092870`. -/

namespace D5.S3.Arith.Robin.FibonacciPrimeSupport

open Finset
open D5.S3.Arith.GoldenResource.RobinRationalBasis
open D5.S3.Arith.Robin.ElevenSmooth
open D5.S3.Arith.Robin.FewDistinctPrimes

/-- `σ(n) · ∏ (p - 1) ≤ n · ∏ p` over the prime factors of `n`. -/
private theorem sigma_mul_le (n : ℕ) (hn : n ≠ 0) :
    ArithmeticFunction.sigma 1 n * ∏ p ∈ n.primeFactors, (p - 1) ≤
      n * ∏ p ∈ n.primeFactors, p := by
  have hps : ∀ p ∈ n.primeFactors.toList, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp hp)
  have hsub : n.primeFactors ⊆ n.primeFactors.toList.toFinset := by
    rw [Finset.toList_toFinset]
  obtain ⟨hpow, hgeom⟩ := factor_repr hps (Finset.nodup_toList _) hn hsub
  have hle := geomProd_le n.primeFactors.toList (n.primeFactors.toList.map n.factorization)
    (fun p hp => (hps p hp).two_le) (by simp)
  rw [hpow, hgeom, Finset.prod_map_toList, Finset.prod_toList] at hle
  exact hle

/-- `σ(n)/n ≤ ∏ p/(p-1)` over the prime factors of `n`. -/
theorem ratio_le_prod (n : ℕ) (hn : n ≠ 0) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n ≤
      ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have hpos : ∀ p ∈ n.primeFactors, (0 : ℝ) < (p : ℝ) - 1 := fun p hp => by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  have hprodpos : (0 : ℝ) < ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := Finset.prod_pos hpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hc1 : ((∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℝ) =
      ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have hcast := (Nat.cast_le (α := ℝ)).mpr (sigma_mul_le n hn)
  rw [Nat.cast_mul, Nat.cast_mul, hc1, Nat.cast_prod] at hcast
  rw [Finset.prod_div_distrib, div_le_div_iff₀ hnR hprodpos]
  linarith

/-- A prime Fibonacci number is at most `5` or has index at least `7`. -/
private theorem fib_prime_cases {p k : ℕ} (hp : p.Prime) (hk : Nat.fib k = p) :
    p ≤ 5 ∨ 7 ≤ k := by
  by_contra h
  rw [not_or, not_le, not_le] at h
  obtain ⟨h5, hk7⟩ := h
  rw [← hk] at hp h5
  revert hp h5
  interval_cases k <;> decide

private theorem three_mul_fib_le (j : ℕ) : 3 * Nat.fib (j + 2) ≤ 2 * Nat.fib (j + 3) := by
  have h1 : Nat.fib (j + 3) = Nat.fib (j + 1) + Nat.fib (j + 2) := Nat.fib_add_two
  have h2 : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
  have h3 : Nat.fib j ≤ Nat.fib (j + 1) := Nat.fib_le_fib_succ
  omega

private theorem fib_ge_thirteen {k : ℕ} (hk : 7 ≤ k) : (13 : ℝ) ≤ Nat.fib k := by
  have h : Nat.fib 7 ≤ Nat.fib k := Nat.fib_mono hk
  have h7 : Nat.fib 7 = 13 := by decide
  exact_mod_cast h7 ▸ h

/-- The reciprocals `1 / (F_k - 1)` for `7 ≤ k < M` telescope below `3 (1/12 - 1/(F_M - 1))`. -/
private theorem recip_sum_le (M : ℕ) (hM : 7 ≤ M) :
    ∑ k ∈ Ico 7 M, 1 / ((Nat.fib k : ℝ) - 1) ≤
      3 * (1 / 12 - 1 / ((Nat.fib M : ℝ) - 1)) := by
  induction M, hM using Nat.le_induction with
  | base => norm_num [Nat.fib_add_two]
  | succ M hM ih =>
    rw [Finset.sum_Ico_succ_top hM]
    obtain ⟨j, rfl⟩ : ∃ j, M = j + 2 := ⟨M - 2, by omega⟩
    have hgrow : (3 : ℝ) * Nat.fib (j + 2) ≤ 2 * Nat.fib (j + 3) := by
      exact_mod_cast three_mul_fib_le j
    have ha := fib_ge_thirteen hM
    have hb := fib_ge_thirteen (by omega : 7 ≤ j + 2 + 1)
    have ha0 : (0 : ℝ) < (Nat.fib (j + 2) : ℝ) - 1 := by linarith
    have hb0 : (0 : ℝ) < (Nat.fib (j + 2 + 1) : ℝ) - 1 := by linarith
    have hstep : 3 * (1 / ((Nat.fib (j + 2 + 1) : ℝ) - 1)) ≤
        2 * (1 / ((Nat.fib (j + 2) : ℝ) - 1)) := by
      rw [mul_one_div, mul_one_div, div_le_div_iff₀ hb0 ha0]
      have : Nat.fib (j + 2 + 1) = Nat.fib (j + 3) := rfl
      rw [this]
      linarith
    linarith

private theorem exp_quarter_lt : Real.exp (1 / 4) < 12841 / 10000 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h4 : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  by_contra hcon
  have hge : (12841 / 10000 : ℝ) ≤ Real.exp (1 / 4) := le_of_not_gt hcon
  have hpow : (12841 / 10000 : ℝ) ^ 4 ≤ Real.exp (1 / 4) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hge 4
  rw [h4] at hpow
  norm_num at hpow h1
  linarith

/-- Prime Fibonacci numbers above `5` contribute at most `e^{1/4}` to `∏ p/(p-1)`. -/
private theorem big_part_le (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ 5 < p ∧ ∃ k, Nat.fib k = p) :
    ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) ≤ Real.exp (1 / 4) := by
  have hfac : ∀ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) ≤ Real.exp (1 / ((p : ℝ) - 1)) := by
    intro p hp
    have h6 : (6 : ℝ) ≤ p := by exact_mod_cast (hS p hp).2.1
    have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have heq : (p : ℝ) / ((p : ℝ) - 1) = 1 / ((p : ℝ) - 1) + 1 := by
      field_simp
      ring
    rw [heq]
    exact Real.add_one_le_exp _
  have hnonneg : ∀ p ∈ S, (0 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have h6 : (6 : ℝ) ≤ p := by exact_mod_cast (hS p hp).2.1
    exact div_nonneg (by linarith) (by linarith)
  set M := S.sup id + 9 with hM
  have hsub : S ⊆ (Ico 7 M).image Nat.fib := by
    intro p hp
    obtain ⟨hprime, h5, k, hk⟩ := hS p hp
    have hk7 : 7 ≤ k := (fib_prime_cases hprime hk).resolve_left (by omega)
    have hkp : k ≤ p + 1 := hk ▸ Nat.le_fib_add_one k
    have hpM : p ≤ S.sup id := by simpa using Finset.le_sup (f := id) hp
    exact Finset.mem_image.mpr ⟨k, Finset.mem_Ico.mpr ⟨hk7, by omega⟩, hk⟩
  have hinj : Set.InjOn Nat.fib (Ico 7 M : Set ℕ) := by
    intro a ha b hb hab
    have ha7 : 7 ≤ a := (Finset.mem_Ico.mp (Finset.mem_coe.mp ha)).1
    have hb7 : 7 ≤ b := (Finset.mem_Ico.mp (Finset.mem_coe.mp hb)).1
    have h := Nat.fib_add_two_strictMono.injective
      (show Nat.fib (a - 2 + 2) = Nat.fib (b - 2 + 2) by
        rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]
        exact hab)
    omega
  have hsum : ∑ p ∈ S, 1 / ((p : ℝ) - 1) ≤ 1 / 4 := by
    have hnn : ∀ p ∈ (Ico 7 M).image Nat.fib, p ∉ S →
        (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := by
      intro p hp _
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
      have := fib_ge_thirteen (Finset.mem_Ico.mp hk).1
      exact div_nonneg zero_le_one (by linarith)
    calc ∑ p ∈ S, 1 / ((p : ℝ) - 1)
        ≤ ∑ p ∈ (Ico 7 M).image Nat.fib, 1 / ((p : ℝ) - 1) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
      _ = ∑ k ∈ Ico 7 M, 1 / ((Nat.fib k : ℝ) - 1) := Finset.sum_image hinj
      _ ≤ 3 * (1 / 12 - 1 / ((Nat.fib M : ℝ) - 1)) := recip_sum_le M (by omega)
      _ ≤ 1 / 4 := by
          have := fib_ge_thirteen (by omega : 7 ≤ M)
          have : (0 : ℝ) ≤ 1 / ((Nat.fib M : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
          linarith
  calc ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1)
      ≤ ∏ p ∈ S, Real.exp (1 / ((p : ℝ) - 1)) := Finset.prod_le_prod₀ hnonneg hfac
    _ = Real.exp (∑ p ∈ S, 1 / ((p : ℝ) - 1)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (1 / 4) := Real.exp_le_exp.mpr hsum

/-- Primes at most `5` contribute at most `2 · 3/2 · 5/4 = 15/4` to `∏ p/(p-1)`. -/
private theorem small_part_le (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ p ≤ 5) :
    ∏ p ∈ T, (p : ℝ) / ((p : ℝ) - 1) ≤ 15 / 4 := by
  classical
  have hsub : T ⊆ {2, 3, 5} := by
    intro p hp
    obtain ⟨hprime, h5⟩ := hT p hp
    have h2 := hprime.two_le
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases p <;> first | decide | (exfalso; norm_num at hprime)
  have hone : ∀ i ∈ ({2, 3, 5} : Finset ℕ), (1 : ℝ) ≤ (i : ℝ) / ((i : ℝ) - 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> norm_num
  rw [← Finset.inter_eq_right.mpr hsub, ← Finset.prod_ite_mem]
  calc ∏ i ∈ ({2, 3, 5} : Finset ℕ), (if i ∈ T then (i : ℝ) / ((i : ℝ) - 1) else 1)
      ≤ ∏ i ∈ ({2, 3, 5} : Finset ℕ), (i : ℝ) / ((i : ℝ) - 1) := by
        refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i hi => ?_)
        · split_ifs
          · exact zero_le_one.trans (hone i hi)
          · exact zero_le_one
        · split_ifs
          · exact le_rfl
          · exact hone i hi
    _ = 15 / 4 := by norm_num

/-- If every prime factor of `n ≠ 0` is a Fibonacci number, then `σ(n)/n < 241/50`. -/
theorem sigma_div_lt_of_fibonacci_primeFactors {n : ℕ} (hn : n ≠ 0)
    (hfib : ∀ p ∈ n.primeFactors, ∃ k, Nat.fib k = p) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n < 241 / 50 := by
  classical
  have hle := ratio_le_prod n hn
  rw [← Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => p ≤ 5)] at hle
  have hsmall := small_part_le (n.primeFactors.filter (fun p => p ≤ 5)) fun p hp => by
    obtain ⟨hp, h5⟩ := Finset.mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors hp, h5⟩
  have hbig := big_part_le (n.primeFactors.filter (fun p => ¬ p ≤ 5)) fun p hp => by
    obtain ⟨hp, h5⟩ := Finset.mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors hp, by omega, hfib p hp⟩
  have hbig0 : (0 : ℝ) ≤ ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ 5),
      (p : ℝ) / ((p : ℝ) - 1) := by
    refine Finset.prod_nonneg fun p hp => ?_
    have h2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
    exact div_nonneg (by linarith) (by linarith)
  have hexp := exp_quarter_lt
  have hexp0 := Real.exp_pos (1 / 4)
  calc (ArithmeticFunction.sigma 1 n : ℝ) / n
      ≤ (∏ p ∈ n.primeFactors.filter (fun p => p ≤ 5), (p : ℝ) / ((p : ℝ) - 1)) *
          ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ 5), (p : ℝ) / ((p : ℝ) - 1) := hle
    _ ≤ 15 / 4 * Real.exp (1 / 4) := mul_le_mul hsmall hbig hbig0 (by norm_num)
    _ < 241 / 50 := by nlinarith

private theorem loglog_two_pow_24 :
    (14 / 5 : ℝ) < Real.log (Real.log ((16777216 : ℕ) : ℝ)) := by
  have h := loglog_of 16777216 (83 / 5) (14 / 5) 1 (83 / 80) 24 4 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)
  exact_mod_cast h

/-- Robin's inequality holds for every `n > 5040` whose prime factors are all Fibonacci numbers.
-/
theorem robin_of_fibonacci_primeFactors {n : ℕ} (hn : 5040 < n)
    (hfib : ∀ p ∈ n.primeFactors, ∃ k, Nat.fib k = p) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) := by
  by_cases hsmall : n < 223092870
  · exact robin_lt_223092870 hn hsmall
  · have hbound := sigma_div_lt_of_fibonacci_primeFactors (by omega) hfib
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hv : 100 * ArithmeticFunction.sigma 1 n ≤ 482 * n := by
      rw [div_lt_iff₀ hnR] at hbound
      have : (100 * ArithmeticFunction.sigma 1 n : ℝ) ≤ 482 * n := by linarith
      exact_mod_cast this
    exact finish (t := 16777216) (K := 482) (l := 14 / 5) (by norm_num) (by omega)
      (by norm_num) loglog_two_pow_24 (by norm_num) hv

end D5.S3.Arith.Robin.FibonacciPrimeSupport
