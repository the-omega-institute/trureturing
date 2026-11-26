/- GID: D5/S3/Arith/FactorialRatio/Compression/UniformQuadratic
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/Compression/UniformQuadratic
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Chebyshev]
   utility: none
   digest: An unconditional uniform quadratic logarithmic bound for compact factorial compression. -/


import D5.S3.Arith.FactorialRatio.Compression.SharpLoss
import D5.S3.Arith.FactorialRatio.QuarticCompactLog
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The compact gcd excess has logarithm at most
`(12 + 19 * log 4) * r^2`, uniformly for `r ≥ 2` and `s < r^2`.
Small primes use the zero parameter. Large primes use a legal integer
near `r / sqrt p`, truncated at `floor(s/p)`. A finite summation-by-parts
estimate converts the large-prime bounds into a quadratic total.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FactorialRatio.Compression.UniformQuadratic

open Finset
open scoped Nat
open D5.S3.Arith.FactorialRatio.RankOneLCMGcd (tailLCM)
open D5.S3.Arith.FactorialRatio.CompactFactorialGcd
open D5.S3.Arith.FactorialRatio.Compression.SharpLoss

private theorem excess_ne_zero {r s : ℕ} (hr : 2 ≤ r) (hs : s < r ^ 2) :
    compactExcess r s ≠ 0 := by
  unfold compactExcess
  exact (Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (selbergGcd_ne_zero r s))
      (compact_factorial_gcd r s hr hs).1)
    (Nat.pos_of_ne_zero (tail_nonzero _ _))).ne'

private theorem excess_zero_above {r s p : ℕ} (hr : 2 ≤ r)
    (hs : s < r ^ 2) (hp : p.Prime) (hsp : s < p) :
    (compactExcess r s).factorization p = 0 := by
  have hzero : (selbergFactorial r s 0).factorization p = 0 := by
    have hlog : Nat.log p s < 1 := by simp [Nat.log_of_lt hsp]
    rw [selberg_factorization hp (by simp : r * 0 ≤ s) hlog,
      Finset.Ico_self, Finset.sum_empty]
  have hg := gcd_factorization_le hp (by omega : 0 < r) (by simp : r * 0 ≤ s)
  rw [compactExcess_factorization hr hs]
  omega

private theorem log_excess_eq_sum {r s : ℕ} (hr : 2 ≤ r) (hs : s < r ^ 2) :
    Real.log (compactExcess r s : ℝ) =
      ∑ p ∈ Nat.primesLE s, ((compactExcess r s).factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  apply Finset.sum_subset
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    refine Nat.mem_primesLE.mpr ⟨?_, hprime⟩
    by_contra h
    have hz := excess_zero_above hr hs hprime (by omega : s < p)
    have hnz : (compactExcess r s).factorization p ≠ 0 := by
      simpa only [← Nat.support_factorization, Finsupp.mem_support_iff] using hp
    exact hnz hz
  · intro p hp hnot
    have hz : (compactExcess r s).factorization p = 0 := by
      simpa only [← Nat.support_factorization, Finsupp.notMem_support_iff] using hnot
    simp [hz]

private theorem excess_le_zero_parameter {r s p : ℕ} (hr : 2 ≤ r)
    (hs : s < r ^ 2) (hp : p.Prime) :
    (compactExcess r s).factorization p ≤ Nat.log p s * (r - 1) := by
  have hbound := selberg_zero_factorization_le_log (s := s) hp (by omega : 1 ≤ r)
  have hg := gcd_factorization_le hp (by omega : 0 < r) (by simp : r * 0 ≤ s)
  rw [compactExcess_factorization hr hs,
    Nat.add_sub_assoc (by omega : 1 ≤ r)]
  omega

private theorem small_prime_sum {r s : ℕ} (hr : 2 ≤ r) (hs : s < r ^ 2) :
    (∑ p ∈ Nat.primesLE r,
      ((compactExcess r s).factorization p : ℝ) * Real.log p) ≤
        3 * (r - 1 : ℕ) * Chebyshev.psi r := by
  rw [Chebyshev.psi_eq_sum_mul_log_prime, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpr, hprime⟩ := Nat.mem_primesLE.mp hp
  have hval := excess_le_zero_parameter hr hs hprime
  have hlog : Nat.log p s ≤ 3 * Nat.log p r := by
    by_cases hs0 : s = 0
    · simp [hs0]
    · exact log_le_three hprime hpr hs0 hs
  have hnat : (compactExcess r s).factorization p ≤
      3 * Nat.log p r * (r - 1) :=
    hval.trans (Nat.mul_le_mul_right _ hlog)
  have hreal : ((compactExcess r s).factorization p : ℝ) ≤
      3 * (Nat.log p r : ℝ) * (r - 1 : ℕ) := by exact_mod_cast hnat
  have hpos : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_le)
  calc
    _ ≤ (3 * (Nat.log p r : ℝ) * (r - 1 : ℕ)) * Real.log p :=
      mul_le_mul_of_nonneg_right hreal hpos
    _ = _ := by ring

private theorem optimized_prime_bound {r s p : ℕ} (hr : 2 ≤ r)
    (hs : s < r ^ 2) (hp : p.Prime) (hrp : r < p) (hps : p ≤ s) :
    ((compactExcess r s).factorization p : ℝ) ≤
      6 * (r : ℝ) / Real.sqrt p + 4 * (r : ℝ) ^ 2 / s := by
  let a : ℝ := (r : ℝ) / Real.sqrt p
  let A : ℕ := ⌊a⌋₊
  let K : ℕ := s / p
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hp.pos.trans_le hps
  have hrR : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hx : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hpR
  have hxsq := Real.sq_sqrt hpR.le
  have hprsq : (p : ℝ) < (r : ℝ) ^ 2 := by exact_mod_cast hps.trans_lt hs
  have hxr : Real.sqrt (p : ℝ) ≤ (r : ℝ) := by nlinarith
  have ha1 : 1 ≤ a := (le_div_iff₀ hx).mpr (by simpa [a] using hxr)
  have hA1 : 1 ≤ A := (Nat.one_le_floor_iff a).mpr ha1
  have hK1 : 1 ≤ K := Nat.div_pos hps hp.pos
  have hA : (A : ℝ) ≤ a := Nat.floor_le (by positivity : 0 ≤ a)
  have hAhalf : a ≤ 2 * (A : ℝ) := by
    have hlt := Nat.lt_floor_add_one a
    have hcast : (1 : ℝ) ≤ A := by exact_mod_cast hA1
    dsimp [A] at hcast ⊢
    linarith
  have hKhalf : (s : ℝ) ≤ 2 * (K : ℝ) * p := by
    have hrem := Nat.mod_lt s hp.pos
    have heq := Nat.div_add_mod s p
    have hkp : p ≤ K * p := Nat.le_mul_of_pos_left p hK1
    have hnat : s ≤ 2 * K * p := by dsimp [K] at *; nlinarith
    exact_mod_cast hnat
  by_cases hAK : A ≤ K
  · have hlegal : A * p ≤ s := by
      exact (Nat.le_div_iff_mul_le hp.pos).mp hAK
    have hlocal := local_prime_excess_bound hr hs hp hrp hlegal hA1
    have hAR : 0 < (A : ℝ) := by exact_mod_cast (by omega : 0 < A)
    have hprod : (r : ℝ) ≤ 2 * (A : ℝ) * Real.sqrt p := by
      have h := (div_le_iff₀ hx).mp hAhalf
      simpa [a] using h
    have hquot : 2 * (r : ℝ) ^ 2 / ((A : ℝ) * p) ≤ 4 * a := by
      dsimp [a]
      rw [show 4 * ((r : ℝ) / Real.sqrt p) =
        (4 * (r : ℝ)) / Real.sqrt p by ring]
      apply (div_le_div_iff₀ (mul_pos hAR hpR) hx).mpr
      have h := mul_le_mul_of_nonneg_left hprod
        (show 0 ≤ 2 * (r : ℝ) * Real.sqrt p by positivity)
      calc
        _ ≤ 4 * (r : ℝ) * (A : ℝ) * (Real.sqrt p) ^ 2 := by nlinarith
        _ = _ := by rw [hxsq]; ring
    have hnon : 0 ≤ 4 * (r : ℝ) ^ 2 / s := by positivity
    calc
      _ ≤ 2 * (A : ℝ) + 2 * (r : ℝ) ^ 2 / ((A : ℝ) * p) := hlocal
      _ ≤ 6 * a := by linarith
      _ ≤ _ := by
        rw [show 6 * (r : ℝ) / Real.sqrt p = 6 * a by dsimp [a]; ring]
        linarith only [hnon]
  · have hKA : K ≤ A := by omega
    have hlocal := local_prime_excess_bound hr hs hp hrp
      ((Nat.le_div_iff_mul_le hp.pos).mp (le_refl K)) hK1
    have hKR : 0 < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
    have hKa : (K : ℝ) ≤ a := (by exact_mod_cast hKA : (K : ℝ) ≤ A).trans hA
    have hquot : 2 * (r : ℝ) ^ 2 / ((K : ℝ) * p) ≤ 4 * (r : ℝ) ^ 2 / s := by
      apply (div_le_div_iff₀ (mul_pos hKR hpR) hsR).mpr
      nlinarith [mul_le_mul_of_nonneg_left hKhalf (sq_nonneg (r : ℝ))]
    have ha0 : 0 ≤ a := by positivity
    calc
      _ ≤ 2 * (K : ℝ) + 2 * (r : ℝ) ^ 2 / ((K : ℝ) * p) := hlocal
      _ ≤ 2 * a + 4 * (r : ℝ) ^ 2 / s := add_le_add (by linarith) hquot
      _ ≤ _ := by
        rw [show 6 * (r : ℝ) / Real.sqrt p = 6 * a by dsimp [a]; ring]
        linarith only [ha0]

private theorem prime_sqrt_sum (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, Real.log p / Real.sqrt p) ≤
      2 * Real.log 4 * Real.sqrt N := by
  let w : ℕ → ℝ := fun n => if n.Prime then Real.log n else 0
  have hsum (n : ℕ) : (∑ i ∈ range (n + 1), w i) = Chebyshev.theta n := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range,
      Finset.sum_filter]
  have h := sum_div_sqrt_le (c := w) (C := Real.log 4) (Real.log_nonneg (by norm_num))
    (by simp [w])
    (fun n => by rw [hsum n]; exact Chebyshev.theta_le_log4_mul_x (by positivity)) N
  simpa only [w, Nat.primesLE_eq_filter_range, Finset.sum_filter,
    ite_div, zero_div] using h

private theorem large_prime_sum {r s : ℕ} (hr : 2 ≤ r) (hs : s < r ^ 2) :
    (∑ p ∈ (Nat.primesLE s).filter (fun p => r < p),
      ((compactExcess r s).factorization p : ℝ) * Real.log p) ≤
        16 * Real.log 4 * (r : ℝ) ^ 2 := by
  by_cases hs0 : s = 0
  · simp [hs0]
    positivity
  have hsR : 0 < (s : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hs0
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hterm :
      (∑ p ∈ (Nat.primesLE s).filter (fun p => r < p),
        ((compactExcess r s).factorization p : ℝ) * Real.log p) ≤
          ∑ p ∈ Nat.primesLE s,
            (6 * (r : ℝ) / Real.sqrt p + 4 * (r : ℝ) ^ 2 / s) * Real.log p := by
    apply le_trans (Finset.sum_le_sum ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun p hp _ => by
          have hprime := Nat.prime_of_mem_primesLE hp
          have hlog := Real.log_nonneg (show (1 : ℝ) ≤ p by exact_mod_cast hprime.one_le)
          positivity))
    intro p hp
    obtain ⟨hpS, hrp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hps, hprime⟩ := Nat.mem_primesLE.mp hpS
    exact mul_le_mul_of_nonneg_right (optimized_prime_bound hr hs hprime hrp hps)
      (Real.log_nonneg (by exact_mod_cast hprime.one_le))
  have hsplit :
      (∑ p ∈ Nat.primesLE s,
        (6 * (r : ℝ) / Real.sqrt p + 4 * (r : ℝ) ^ 2 / s) * Real.log p) =
          6 * (r : ℝ) * (∑ p ∈ Nat.primesLE s, Real.log p / Real.sqrt p) +
          (4 * (r : ℝ) ^ 2 / s) * Chebyshev.theta s := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have htheta := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ s by positivity)
  have hroot : Real.sqrt (s : ℝ) ≤ (r : ℝ) := by
    have hsq := Real.sq_sqrt hsR.le
    have hsr : (s : ℝ) < (r : ℝ) ^ 2 := by exact_mod_cast hs
    nlinarith [Real.sqrt_nonneg (s : ℝ), show (0 : ℝ) ≤ r by positivity]
  calc
    _ ≤ _ := hterm
    _ = _ := hsplit
    _ ≤ 6 * (r : ℝ) * (2 * Real.log 4 * Real.sqrt s) +
        (4 * (r : ℝ) ^ 2 / s) * (Real.log 4 * s) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (prime_sqrt_sum s) (by positivity))
        (mul_le_mul_of_nonneg_left htheta (by positivity))
    _ = 12 * Real.log 4 * (r : ℝ) * Real.sqrt s +
        4 * Real.log 4 * (r : ℝ) ^ 2 := by field_simp [ne_of_gt hsR]; ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hroot
        (show 0 ≤ 12 * Real.log 4 * (r : ℝ) by positivity)
      nlinarith

/-- Uniform quadratic logarithmic loss, including `s = 0` and the range
`s < r` where the compact family consists of its zero parameter. The
constant `12 + 19 log 4` equals `12 + 38 log 2`. -/
theorem uniform_quadratic_log_bound (r s : ℕ) (hr : 2 ≤ r)
    (hs : s < r ^ 2) :
    0 ≤ Real.log (compactExcess r s : ℝ) ∧
      Real.log (compactExcess r s : ℝ) ≤ (12 + 19 * Real.log 4) * (r : ℝ) ^ 2 := by
  constructor
  · apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (excess_ne_zero hr hs)
  have hsmall := small_prime_sum hr hs
  have hlarge := large_prime_sum hr hs
  have hsplit :
      (∑ p ∈ Nat.primesLE s, ((compactExcess r s).factorization p : ℝ) * Real.log p) ≤
        (∑ p ∈ Nat.primesLE r, ((compactExcess r s).factorization p : ℝ) * Real.log p) +
        ∑ p ∈ (Nat.primesLE s).filter (fun p => r < p),
          ((compactExcess r s).factorization p : ℝ) * Real.log p := by
    rw [← Finset.sum_filter_add_sum_filter_not (Nat.primesLE s) (fun p => p ≤ r)]
    have hleft :
        (∑ p ∈ (Nat.primesLE s).filter (fun p => p ≤ r),
          ((compactExcess r s).factorization p : ℝ) * Real.log p) ≤
            ∑ p ∈ Nat.primesLE r,
              ((compactExcess r s).factorization p : ℝ) * Real.log p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hpS, hpr⟩ := Finset.mem_filter.mp hp
        exact Nat.mem_primesLE.mpr ⟨hpr, Nat.prime_of_mem_primesLE hpS⟩
      · intro p hp _
        have hprime := Nat.prime_of_mem_primesLE hp
        exact mul_nonneg (by positivity)
          (Real.log_nonneg (by exact_mod_cast hprime.one_le))
    simpa only [not_le] using add_le_add_left hleft
      (∑ p ∈ (Nat.primesLE s).filter (fun p => ¬p ≤ r),
        ((compactExcess r s).factorization p : ℝ) * Real.log p)
  have hpsi := Chebyshev.psi_le_const_mul_self (show (0 : ℝ) ≤ r by positivity)
  have hsmall' : 3 * (r - 1 : ℕ) * Chebyshev.psi r ≤
      3 * (Real.log 4 + 4) * (r : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hpsi
      (show (0 : ℝ) ≤ 3 * (r - 1 : ℕ) by positivity)
    have hsub : ((r - 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
    have hcoef : 0 ≤ 3 * (Real.log 4 + 4) * (r : ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_left hsub hcoef
    nlinarith
  rw [log_excess_eq_sum hr hs]
  calc
    _ ≤ _ := hsplit
    _ ≤ 3 * (r - 1 : ℕ) * Chebyshev.psi r +
        16 * Real.log 4 * (r : ℝ) ^ 2 := add_le_add hsmall hlarge
    _ ≤ 3 * (Real.log 4 + 4) * (r : ℝ) ^ 2 +
        16 * Real.log 4 * (r : ℝ) ^ 2 := add_le_add_left hsmall' _
    _ = _ := by ring

end D5.S3.Arith.FactorialRatio.Compression.UniformQuadratic
