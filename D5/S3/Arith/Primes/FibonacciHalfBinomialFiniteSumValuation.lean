/- GID: D5/S3/Arith/Primes/FibonacciHalfBinomialFiniteSumValuation
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciHalfBinomialFiniteSumValuation
   mirror-E: none(waiver:algebraically-proved)
   anchors: [D5/S3/Arith/Primes/FibonacciHalfBinomialValuation]
   utility: none
   digest: Dyadic dominance of the last term in a finite half-binomial sum. -/

import D5.S3.Arith.Primes.FibonacciHalfBinomialValuation
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.FibonacciHalfBinomialFiniteSumValuation

open Finset
open D5.S3.Arith.Primes.FibonacciHalfBinomialValuation

theorem half_binomial_finite_sum_valuation (n : ℕ) (hn : 1 ≤ n)
    (c : ℕ → ℤ) (hc : Odd (c n)) :
    padicValRat 2
        (∑ m ∈ Finset.range (n + 1), Ring.choose (1/2 : ℚ) m * (c m : ℚ)) =
      -((n : ℤ) + padicValNat 2 n.factorial) := by
  classical
  let e : ℕ → ℤ := fun m => (m : ℤ) + padicValNat 2 m.factorial
  let term : ℕ → ℚ := fun m => Ring.choose (1/2 : ℚ) m * (c m : ℚ)
  change padicValRat 2 (∑ m ∈ Finset.range (n + 1), term m) = -e n
  have hepos : 0 < e n := by
    dsimp [e]
    omega
  have hfacmono (m k : ℕ) (hmk : m ≤ k) :
      padicValNat 2 m.factorial ≤ padicValNat 2 k.factorial := by
    obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial hmk
    have ht0 : t ≠ 0 := by
      intro hz
      have hkzero : k.factorial = 0 := by simp [ht, hz]
      exact Nat.factorial_ne_zero k hkzero
    rw [ht, padicValNat.mul (Nat.factorial_ne_zero m) ht0]
    omega
  have he_strict (m : ℕ) (hm : m < n) : -e n < -e m := by
    have hfac := hfacmono m n hm.le
    dsimp [e]
    omega
  have hcodd : ¬ (2 : ℤ) ∣ c n := by
    rcases hc with ⟨k, hk⟩
    intro ⟨t, ht⟩
    omega
  have hcne : (c n : ℚ) ≠ 0 := by
    intro hz
    have hzero : c n = 0 := by exact_mod_cast hz
    exact hcodd (by rw [hzero]; exact dvd_zero 2)
  have hchoose_ne : Ring.choose (1/2 : ℚ) n ≠ 0 := by
    intro hz
    have hv := half_binomial_two_adic_valuation n
    rw [hz] at hv
    norm_num at hv
    omega
  have hlast_ne : term n ≠ 0 := mul_ne_zero hchoose_ne hcne
  have hlast_val : padicValRat 2 (term n) = -e n := by
    dsimp [term, e]
    rw [padicValRat.mul hchoose_ne hcne,
      half_binomial_two_adic_valuation, padicValRat.of_int,
      padicValInt.eq_zero_of_not_dvd hcodd]
    omega
  have hbound (m : ℕ) (hm : m < n) :
      -e n < padicValRat 2 (term m) := by
    by_cases hzero : term m = 0
    · rw [hzero]
      simp
      omega
    · have hnonzero := mul_ne_zero_iff.mp hzero
      have hnonneg : 0 ≤ padicValRat 2 (c m : ℚ) := by
        rw [padicValRat.of_int]
        exact Nat.cast_nonneg _
      have hval : padicValRat 2 (term m) =
          -e m + padicValRat 2 (c m : ℚ) := by
        dsimp [term, e]
        rw [padicValRat.mul hnonzero.1 hnonzero.2,
          half_binomial_two_adic_valuation]
      rw [hval]
      have hs := he_strict m hm
      omega
  have hprefix (k : ℕ) (hk : k ≤ n) :
      -e n < padicValRat 2 (∑ m ∈ Finset.range k, term m) := by
    induction k with
    | zero =>
        simp
        omega
    | succ k ih =>
        rw [Finset.sum_range_succ]
        by_cases hsum : (∑ m ∈ Finset.range k, term m) + term k = 0
        · rw [hsum]
          simp
          omega
        · exact lt_of_lt_of_le
            (lt_min (ih (by omega)) (hbound k (by omega)))
            (padicValRat.min_le_padicValRat_add hsum)
  have htail := hprefix n le_rfl
  have hsum_ne : (∑ m ∈ Finset.range n, term m) + term n ≠ 0 := by
    intro hz
    have ht : (∑ m ∈ Finset.range n, term m) = -term n := by
      linear_combination hz
    have hv := congrArg (padicValRat 2) ht
    rw [padicValRat.neg, hlast_val] at hv
    omega
  rw [Finset.sum_range_succ]
  by_cases htail_zero : (∑ m ∈ Finset.range n, term m) = 0
  · simpa [htail_zero] using hlast_val
  · rw [add_comm]
    exact padicValRat.add_eq_of_lt
      (by simpa only [add_comm] using hsum_ne) hlast_ne htail_zero
      (by rw [hlast_val]; exact htail) |>.trans hlast_val

#print axioms half_binomial_finite_sum_valuation

end D5.S3.Arith.Primes.FibonacciHalfBinomialFiniteSumValuation
