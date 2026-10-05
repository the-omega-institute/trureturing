/- GID: D5/S3/Arith/Robin/FibonacciRankSizeDecomposition
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/FibonacciRankSizeDecomposition
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: A common index splits the Fibonacci Euler ratio into small ranks and a bounded tail. -/

import D5.S3.Arith.Robin.FibonacciRankEulerTail
import D5.S3.Arith.FibonacciAtomic.TimeSampling
import Mathlib.Data.Nat.Totient

namespace D5.S3.Arith.Robin.FibonacciRankSizeDecomposition

open Finset
open D5.S3.Arith.FibonacciRank
open D5.S3.Arith.FibonacciAtomic.TimeSampling
open D5.S3.Arith.Robin.FibonacciRankEulerTail

/-- The product of Fibonacci numbers at the small divisors supplies exactly
the small-rank Euler factors. The remaining logarithmic mass is bounded by
the number of divisors of the common index. -/
theorem result (j : ℕ) (Y : ℝ) (hj : 3 ≤ j) (hY : 5 ≤ Y)
    (hA : 2 ≤ ∏ d ∈ j.divisors.filter (fun d => (d : ℝ) ≤ Y), Nat.fib d) :
    let A := ∏ d ∈ j.divisors.filter (fun d => (d : ℝ) ≤ Y), Nat.fib d
    ∃ R : ℝ,
      (Nat.fib j : ℝ) / (Nat.totient (Nat.fib j) : ℝ) =
        (A : ℝ) / (Nat.totient A : ℝ) * Real.exp R ∧
      0 ≤ R ∧ R ≤ 6 * (j.divisors.card : ℝ) * (1 + Real.log Y) / Y := by
  classical
  let smallD := j.divisors.filter (fun d => (d : ℝ) ≤ Y)
  let largeD := j.divisors.filter (fun d => ¬ (d : ℝ) ≤ Y)
  let A := ∏ d ∈ smallD, Nat.fib d
  let primes := (Nat.fib j).primeFactors
  let low := primes.filter (fun p => (zeroRank p : ℝ) ≤ Y)
  let high := primes.filter (fun p => ¬ (zeroRank p : ℝ) ≤ Y)
  let factor : ℕ → ℝ := fun p => (p : ℝ) / ((p : ℝ) - 1)
  let mass : ℕ → ℝ := fun p => Real.log (factor p)
  have hj0 : j ≠ 0 := by omega
  have hfib0 : Nat.fib j ≠ 0 := (Nat.fib_pos.mpr (by omega)).ne'
  have hA0 : A ≠ 0 := by dsimp [A, smallD]; omega
  have hY0 : 0 < Y := by linarith
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have entry (p : ℕ) (hp : p.Prime) (n : ℕ) :
      p ∣ Nat.fib n ↔ zeroRank p ∣ n := by
    have hz := prime_zero_rank_facts p hp
    exact fibonacci_entry_point hz.1 hz.2.1 hz.2.2
  have small_support (p : ℕ) (hp : p.Prime) :
      p ∣ A ↔ p ∣ Nat.fib j ∧ (zeroRank p : ℝ) ≤ Y := by
    constructor
    · intro hpA
      obtain ⟨d, hd, hpd⟩ := (hp.prime.dvd_finsetProd_iff Nat.fib).mp hpA
      obtain ⟨hdj, hdY⟩ := Finset.mem_filter.mp hd
      have hdvd := (Nat.mem_divisors.mp hdj).1
      have hdpos := Nat.pos_of_mem_divisors hdj
      have hzle := (prime_zero_rank_facts p hp).2.2 d hdpos hpd
      exact ⟨(entry p hp j).mpr (dvd_trans ((entry p hp d).mp hpd) hdvd),
        (Nat.cast_le.mpr hzle).trans hdY⟩
    · rintro ⟨hpj, hpY⟩
      apply (hp.prime.dvd_finsetProd_iff Nat.fib).mpr
      refine ⟨zeroRank p, ?_, (prime_zero_rank_facts p hp).2.1⟩
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨(entry p hp j).mp hpj, hj0⟩, hpY⟩
  have low_support : low = A.primeFactors := by
    ext p
    simp only [low, primes, Finset.mem_filter, Nat.mem_primeFactors, hfib0, hA0,
      and_true]
    constructor
    · rintro ⟨⟨hp, hpj⟩, hpY⟩
      exact ⟨hp, (small_support p hp).mpr ⟨hpj, hpY⟩⟩
    · rintro ⟨hp, hpA⟩
      exact ⟨⟨hp, ((small_support p hp).mp hpA).1⟩,
        ((small_support p hp).mp hpA).2⟩
  have high_maps (p : ℕ) (hp : p ∈ high) : zeroRank p ∈ largeD := by
    obtain ⟨hpj, hpY⟩ := Finset.mem_filter.mp hp
    have hprime := Nat.prime_of_mem_primeFactors hpj
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨(entry p hprime j).mp (Nat.dvd_of_mem_primeFactors hpj),
        hj0⟩, hpY⟩
  have fiber (d : ℕ) (hd : d ∈ largeD) :
      high.filter (fun p => zeroRank p = d) = rankBucket d := by
    have hdj := (Finset.mem_filter.mp hd).1
    have hdY : Y < (d : ℝ) := lt_of_not_ge (Finset.mem_filter.mp hd).2
    have hdpos := Nat.pos_of_mem_divisors hdj
    ext p
    constructor
    · intro hp
      obtain ⟨hpH, heq⟩ := Finset.mem_filter.mp hp
      have hpj := (Finset.mem_filter.mp hpH).1
      have hprime := Nat.prime_of_mem_primeFactors hpj
      have hz := prime_zero_rank_facts p hprime
      have hpd : p ∣ Nat.fib d := heq ▸ hz.2.1
      simp only [rankBucket, Finset.mem_filter]
      refine ⟨Nat.mem_primeFactors.mpr ⟨hprime, hpd, (Nat.fib_pos.mpr hdpos).ne'⟩, ?_⟩
      intro k hk hpk
      have hkle := hz.2.2 k (by have := (Finset.mem_Ico.mp hk).1; omega) hpk
      have hklt := (Finset.mem_Ico.mp hk).2
      omega
    · intro hp
      have hpd := (Finset.mem_filter.mp hp).1
      have hprime := Nat.prime_of_mem_primeFactors hpd
      have hz := prime_zero_rank_facts p hprime
      have heq : zeroRank p = d := Nat.le_antisymm
        (hz.2.2 d hdpos (Nat.dvd_of_mem_primeFactors hpd))
        (rank_bucket_min d p hp (zeroRank p) hz.1 hz.2.1)
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, heq⟩
      · exact Nat.mem_primeFactors.mpr ⟨hprime,
          dvd_trans (Nat.dvd_of_mem_primeFactors hpd)
            (Nat.fib_dvd d j (Nat.mem_divisors.mp hdj).1), hfib0⟩
      · simpa only [heq, not_le] using hdY
  have regroup : (∑ p ∈ high, mass p) =
      ∑ d ∈ largeD, ∑ p ∈ rankBucket d, mass p := by
    rw [← Finset.sum_fiberwise_of_maps_to high_maps]
    apply Finset.sum_congr rfl
    intro d hd
    rw [fiber d hd]
  have cutoff_bound (d : ℕ) (hd : d ∈ largeD) :
      6 * (1 + Real.log d) / d ≤ 6 * (1 + Real.log Y) / Y := by
    have hYd : Y < (d : ℝ) := lt_of_not_ge (Finset.mem_filter.mp hd).2
    have hd0 : (0 : ℝ) < d := hY0.trans hYd
    have hlog : Real.log d - Real.log Y ≤ (d : ℝ) / Y - 1 := by
      rw [← Real.log_div hd0.ne' hY0.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hd0 hY0)
    have hscaled := mul_le_mul_of_nonneg_left hlog hY0.le
    have hcancel : Y * ((d : ℝ) / Y - 1) = (d : ℝ) - Y := by
      field_simp
    rw [hcancel] at hscaled
    apply (div_le_div_iff₀ hd0 hY0).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hYd.le) hlogY]
  have bucket_bound (d : ℕ) (hd : d ∈ largeD) :
      (∑ p ∈ rankBucket d, mass p) ≤ 6 * (1 + Real.log Y) / Y := by
    have hYd : Y < (d : ℝ) := lt_of_not_ge (Finset.mem_filter.mp hd).2
    have hd5 : 5 < d := by exact_mod_cast (show (5 : ℝ) < d by linarith)
    exact ((D5.S3.Arith.Robin.FibonacciRankEulerTail.result d hd5).1.trans
      (D5.S3.Arith.Robin.FibonacciRankEulerTail.result d hd5).2).trans
        (cutoff_bound d hd)
  have remainder_bound : (∑ p ∈ high, mass p) ≤
      6 * (j.divisors.card : ℝ) * (1 + Real.log Y) / Y := by
    rw [regroup]
    calc
      _ ≤ ∑ _d ∈ largeD, 6 * (1 + Real.log Y) / Y := Finset.sum_le_sum bucket_bound
      _ = (largeD.card : ℝ) * (6 * (1 + Real.log Y) / Y) := by simp
      _ ≤ (j.divisors.card : ℝ) * (6 * (1 + Real.log Y) / Y) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_filter_le _ _))
          (by positivity)
      _ = _ := by ring
  have factor_pos (p : ℕ) (hp : p.Prime) : 0 < factor p := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    dsimp [factor]
    exact div_pos (by linarith) (by linarith)
  have euler_ratio (n : ℕ) (hn : n ≠ 0) :
      (n : ℝ) / (Nat.totient n : ℝ) = ∏ p ∈ n.primeFactors, factor p := by
    have ht : (Nat.totient n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
    have hden : (∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      linarith
    have heuler : (Nat.totient n : ℝ) * (∏ p ∈ n.primeFactors, (p : ℝ)) =
        (n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
      have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.totient_mul_prod_primeFactors n)
      push_cast at h
      convert h using 2
      apply Finset.prod_congr rfl
      intro p hp
      exact (Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le).symm
    dsimp only [factor]
    rw [Finset.prod_div_distrib]
    apply (div_eq_div_iff ht hden).mpr
    nlinarith [heuler]
  have exponential : Real.exp (∑ p ∈ high, mass p) = ∏ p ∈ high, factor p := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro p hp
    exact Real.exp_log (factor_pos p
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1))
  refine ⟨∑ p ∈ high, mass p, ?_, ?_, remainder_bound⟩
  · change (Nat.fib j : ℝ) / (Nat.totient (Nat.fib j) : ℝ) =
      (A : ℝ) / (Nat.totient A : ℝ) * Real.exp (∑ p ∈ high, mass p)
    rw [euler_ratio (Nat.fib j) hfib0, euler_ratio A hA0, exponential, ← low_support]
    exact (Finset.prod_filter_mul_prod_filter_not primes
      (fun p => (zeroRank p : ℝ) ≤ Y) factor).symm
  · apply Finset.sum_nonneg
    intro p hp
    exact (euler_log_bounds p
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le).1

end D5.S3.Arith.Robin.FibonacciRankSizeDecomposition
