/- GID: D5/S3/Arith/Congruence/OddLucasSquareFibonacciDivisors
   generality: G
   mirror-B: none(waiver:source-anchored-universal-classification)
   mirror-E: none(waiver:two-external-conjectures-one-proof-family)
   anchors: []
   digest: Every Fibonacci divisor of an odd-index Lucas square plus one is 1 or 2; the exact divisor set proves both conjectures in OEIS A339669. -/

import D5.S1.Scale.Lucas
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.Congruence.OddLucasSquareFibonacciDivisors

open D5.S0.Carrier D5.S1.Scale

/-- The integer in the external problem, using the existing algebraic Lucas trace. -/
def target (n : ℕ) : ℕ := (goldenLucas n ^ 2 + 1).toNat

lemma target_cast (n : ℕ) : (target n : ℤ) = goldenLucas n ^ 2 + 1 :=
  Int.toNat_of_nonneg (by positivity)

lemma target_pos (n : ℕ) : 0 < target n := by
  have h : (0 : ℤ) < (target n : ℤ) := by rw [target_cast]; positivity
  exact_mod_cast h

/-- Distinct Fibonacci VALUES are counted. F_1=F_2=1 contributes once. -/
noncomputable def fibonacciDivisors (m : ℕ) : Finset ℕ := by
  classical
  exact m.divisors.filter (fun d => ∃ k : ℕ, Nat.fib k = d)

noncomputable def a339669 (n : ℕ) : ℕ := (fibonacciDivisors (target n)).card

/-- The cube coordinate identity in the original golden ring. -/
lemma cube_b (x : GoldenInt) :
    (x ^ 3).b = x.b * (trace x ^ 2 - norm x) := by
  simp only [pow_succ, pow_zero, one_mul, mul_one, b_mul, a_mul, trace, norm]
  ring

/-- Oddness changes the Lucas tripling factor into precisely L_n^2+1. -/
theorem odd_tripling (n : ℕ) (hn : Odd n) :
    Nat.fib (3 * n) = Nat.fib n * target n := by
  have h := cube_b (phi ^ n)
  rw [← pow_mul, golden_phi_pow_b_eq_fib_index,
    golden_phi_pow_b_eq_fib_index, norm_phi_pow, hn.neg_one_pow] at h
  have hi : (Nat.fib (3 * n) : ℤ) = (Nat.fib n : ℤ) * (target n : ℤ) := by
    rw [target_cast]
    simpa only [goldenLucas, Nat.mul_comm, sub_neg_eq_add] using h
  exact_mod_cast hi

lemma target_add_three (n : ℕ) (hn : Odd n) :
    target n + 3 = 5 * Nat.fib n ^ 2 := by
  have h := golden_lucas_discriminant n
  rw [hn.neg_one_pow] at h
  have hi : (target n : ℤ) + 3 = 5 * (Nat.fib n : ℤ) ^ 2 := by
    rw [target_cast]
    nlinarith
  exact_mod_cast hi

lemma odd_fib_coprime_three (n : ℕ) (hn : Odd n) :
    Nat.Coprime (Nat.fib n) 3 := by
  have hc : Nat.Coprime n 4 := by
    simpa using hn.coprime_two_right.pow_right 2
  have h := Nat.fib_gcd n 4
  rw [hc.gcd_eq_one] at h
  norm_num [Nat.fib] at h
  exact h.symm

/-- The tripling quotient shares no prime factor with F_n at odd n. -/
theorem target_coprime_fib (n : ℕ) (hn : Odd n) :
    Nat.Coprime (Nat.fib n) (target n) := by
  let d := Nat.gcd (Nat.fib n) (target n)
  have hdF : d ∣ Nat.fib n := Nat.gcd_dvd_left _ _
  have hdM : d ∣ target n := Nat.gcd_dvd_right _ _
  have hdSquare : d ∣ Nat.fib n ^ 2 := by
    simpa only [pow_two] using dvd_mul_of_dvd_left hdF (Nat.fib n)
  have hdSum : d ∣ target n + 3 := by
    rw [target_add_three n hn]
    exact dvd_mul_of_dvd_right hdSquare 5
  have hd3 : d ∣ 3 := by
    have h1 : (d : ℤ) ∣ (target n : ℤ) + 3 := by exact_mod_cast hdSum
    have h2 : (d : ℤ) ∣ (target n : ℤ) := by exact_mod_cast hdM
    have hh : (d : ℤ) ∣ 3 := by simpa using dvd_sub h1 h2
    exact_mod_cast hh
  exact Nat.eq_one_of_dvd_coprimes (odd_fib_coprime_three n hn) hdF hd3

/-- Fibonacci coprimality descends to index coprimality when the second index is odd.
The F_1=F_2 ambiguity is handled explicitly, rather than assuming a false injectivity law. -/
lemma index_coprime_of_odd (k n : ℕ) (hn : Odd n)
    (hc : Nat.Coprime (Nat.fib k) (Nat.fib n)) : Nat.Coprime k n := by
  have hf : Nat.fib (Nat.gcd k n) = 1 := by rw [Nat.fib_gcd, hc.gcd_eq_one]
  have hsmall : Nat.gcd k n ≤ 2 := by
    have h := Nat.le_fib_add_one (Nat.gcd k n)
    rw [hf] at h
    omega
  obtain ⟨u, hu⟩ := Nat.gcd_dvd_right k n
  obtain ⟨v, hv⟩ := hn
  change Nat.gcd k n = 1
  by_contra h
  have hh : Nat.gcd k n = 0 ∨ Nat.gcd k n = 2 := by omega
  rcases hh with hd | hd <;> rw [hd] at hu <;> omega

/-- Strong classification: every Fibonacci divisor of an odd Lucas square plus one divides 2. -/
theorem fibonacci_divisor_dvd_two (n k : ℕ) (hn : Odd n)
    (hdiv : Nat.fib k ∣ target n) : Nat.fib k ∣ 2 := by
  have hcop : Nat.Coprime (Nat.fib k) (Nat.fib n) :=
    (target_coprime_fib n hn).symm.of_dvd_left hdiv
  have hkn : Nat.Coprime k n := index_coprime_of_odd k n hn hcop
  have ht : Nat.fib k ∣ Nat.fib (3 * n) := by
    rw [odd_tripling n hn]
    exact dvd_mul_of_dvd_right hdiv (Nat.fib n)
  have hg : Nat.fib (Nat.gcd k (3 * n)) = Nat.fib k := by
    rw [Nat.fib_gcd, Nat.gcd_eq_left ht]
  have hd : Nat.gcd k (3 * n) ∣ 3 :=
    (hkn.of_dvd_left (Nat.gcd_dvd_left k (3 * n))).dvd_of_dvd_mul_right
      (Nat.gcd_dvd_right k (3 * n))
  have h := Nat.fib_dvd hd
  rw [hg] at h
  simpa [Nat.fib] using h

lemma two_dvd_fib_iff (n : ℕ) : 2 ∣ Nat.fib n ↔ 3 ∣ n := by
  constructor
  · intro hn
    have hd : Nat.fib 3 ∣ Nat.fib n := by simpa [Nat.fib] using hn
    have hcases : Nat.gcd 3 n = 1 ∨ Nat.gcd 3 n = 3 :=
      (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 n)
    rcases hcases with h | h
    · have hf := Nat.fib_gcd 3 n
      rw [h, Nat.gcd_eq_left hd] at hf
      norm_num [Nat.fib] at hf
    · simpa only [h] using Nat.gcd_dvd_right 3 n
  · intro hn
    simpa [Nat.fib] using Nat.fib_dvd hn

lemma two_dvd_target_iff (n : ℕ) (hn : Odd n) :
    2 ∣ target n ↔ ¬ 3 ∣ n := by
  rw [← two_dvd_fib_iff]
  have h := congrArg (fun x : ℕ => x % 2) (target_add_three n hn)
  have hF := Nat.mod_lt (Nat.fib n) (by decide : 0 < 2)
  have hM := Nat.mod_lt (target n) (by decide : 0 < 2)
  simp only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at h
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
  rcases (show Nat.fib n % 2 = 0 ∨ Nat.fib n % 2 = 1 by omega) with hh | hh <;>
    rw [hh] at h <;> norm_num at h <;> omega

/-- Exact membership, with a positive target and distinct-value convention. -/
theorem odd_fibonacci_divisors_mem (n d : ℕ) (hn : Odd n) :
    d ∈ fibonacciDivisors (target n) ↔ d = 1 ∨ (d = 2 ∧ ¬ 3 ∣ n) := by
  classical
  simp only [fibonacciDivisors, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, _⟩, ⟨k, hk⟩⟩
    have hf : Nat.fib k ∣ target n := by simpa only [hk] using hd
    have hd2 : d ∣ 2 := by simpa only [hk] using fibonacci_divisor_dvd_two n k hn hf
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, (two_dvd_target_iff n hn).mp (by simpa only [h] using hd)⟩
  · rintro (rfl | ⟨rfl, h⟩)
    · exact ⟨⟨one_dvd _, ne_of_gt (target_pos n)⟩, ⟨1, Nat.fib_one⟩⟩
    · exact ⟨⟨(two_dvd_target_iff n hn).mpr h, ne_of_gt (target_pos n)⟩,
        ⟨3, by norm_num [Nat.fib]⟩⟩

/-- The whole divisor set is classified, not only its cardinality. -/
theorem odd_fibonacci_divisors (n : ℕ) (hn : Odd n) :
    fibonacciDivisors (target n) = if 3 ∣ n then {1} else {1, 2} := by
  classical
  ext d
  rw [odd_fibonacci_divisors_mem n d hn]
  by_cases h : 3 ∣ n <;> simp [h]

theorem odd_count (n : ℕ) (hn : Odd n) : a339669 n = if 3 ∣ n then 1 else 2 := by
  classical
  unfold a339669
  rw [odd_fibonacci_divisors n hn]
  by_cases h : 3 ∣ n <;> simp [h]

/-- OEIS A339669, Michel Lagneau (2020), Conjecture 1, for every natural t. -/
theorem lagneau_conjecture_one (t : ℕ) : a339669 (6 * t + 3) = 1 := by
  have ho : Odd (6 * t + 3) := ⟨3 * t + 1, by omega⟩
  have hd : 3 ∣ 6 * t + 3 := ⟨2 * t + 1, by omega⟩
  rw [odd_count _ ho, if_pos hd]

/-- OEIS A339669, Michel Lagneau (2020), Conjecture 2, kept as its one original joint claim. -/
theorem lagneau_conjecture_two (t : ℕ) :
    a339669 (6 * t + 1) = 2 ∧ a339669 (6 * t + 5) = 2 := by
  have h1 : Odd (6 * t + 1) := ⟨3 * t, by omega⟩
  have h5 : Odd (6 * t + 5) := ⟨3 * t + 2, by omega⟩
  have hn1 : ¬ 3 ∣ 6 * t + 1 := by rintro ⟨k, hk⟩; omega
  have hn5 : ¬ 3 ∣ 6 * t + 5 := by rintro ⟨k, hk⟩; omega
  rw [odd_count _ h1, odd_count _ h5, if_neg hn1, if_neg hn5]
  exact ⟨rfl, rfl⟩

end D5.S3.Arith.Congruence.OddLucasSquareFibonacciDivisors
