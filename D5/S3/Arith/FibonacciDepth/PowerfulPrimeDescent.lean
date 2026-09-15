/- GID: D5/S3/Arith/FibonacciDepth/PowerfulPrimeDescent
   generality: G
   mirror-B: none(waiver:all-positive-counterexample-indices)
   mirror-E: none(waiver:constructive-prime-index-descent)
   anchors: []
   digest: Every nonclassical powerful Fibonacci value descends to its largest prime index. -/

import D5.S3.Arith.FibonacciDepth.PrimeSquareTransport
import D5.S3.Arith.FibonacciRank
import D5.S0.Carrier.ArithmeticFunctions.PowerfulDivisorTransform
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Max

set_option autoImplicit false

namespace D5.S3.Arith.FibonacciDepth.PowerfulPrimeDescent

open D5.S3.Arith.FibonacciDepth.PrimeSquareTransport
open D5.S3.Arith.FibonacciRank
open D5.S0.Carrier.ArithmeticFunctions.PowerfulDivisorTransform

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private lemma small_prime_cases (p : ℕ) (hp : p.Prime) (hle : p ≤ 5) :
    p = 2 ∨ p = 3 ∨ p = 5 := by
  interval_cases p <;> norm_num at hp ⊢

/-- An actual simple Fibonacci factor survives if its prime is absent from the index. -/
private lemma simple_factor_survives (p d m : ℕ) (hp : p.Prime) (hd : 0 < d)
    (hpf : p ∣ Nat.fib d) (hsimple : ¬p ^ 2 ∣ Nat.fib d)
    (hdm : d ∣ m) (hpm : ¬p ∣ m) : ¬p ^ 2 ∣ Nat.fib m := by
  obtain ⟨k, rfl⟩ := hdm
  intro hsq
  rcases (prime_square_fib_mul_iff p d k hp hd hpf).mp hsq with h | h
  · exact hsimple h
  · exact hpm (h.mul_left d)

/-- The finite exceptional support is derived, not assumed as a valuation table. -/
private lemma five_smooth_powerful (m : ℕ) (hm : 0 < m)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ m → p ≤ 5)
    (hpower : Powerful (Nat.fib m)) : m = 1 ∨ m = 2 ∨ m = 6 ∨ m = 12 := by
  have hm0 : m ≠ 0 := by omega
  have hlarge : ∀ p : ℕ, p.Prime → 5 < p → ¬p ∣ m := by
    intro p hp hbig hdiv
    have := hsupport p hp hdiv
    omega
  have h25 : ¬25 ∣ m := by
    intro hdiv
    have hf := simple_factor_survives 3001 25 m (by norm_num) (by omega)
      (by decide +kernel) (by decide +kernel) hdiv
      (hlarge 3001 (by norm_num) (by omega))
    have h3001 : 3001 ∣ Nat.fib m :=
      dvd_trans (by decide +kernel : 3001 ∣ Nat.fib 25) (Nat.fib_dvd 25 m hdiv)
    exact hf (hpower.2 3001 (by norm_num) h3001)
  have h5 : ¬5 ∣ m := by
    intro hdiv
    obtain ⟨k, hk⟩ := hdiv
    have hnk : ¬5 ∣ k := by
      intro h
      obtain ⟨u, hu⟩ := h
      apply h25
      exact ⟨u, by rw [hk, hu]; ring⟩
    have h5f : 5 ∣ Nat.fib m :=
      dvd_trans (by decide +kernel : 5 ∣ Nat.fib 5) (Nat.fib_dvd 5 m ⟨k, hk⟩)
    have hs := hpower.2 5 Nat.prime_five h5f
    rw [hk] at hs
    rcases (prime_square_fib_mul_iff 5 5 k Nat.prime_five (by omega)
      (by decide +kernel)).mp hs with h | h
    · norm_num [Nat.fib_add_two] at h
    · exact hnk h
  have h9 : ¬9 ∣ m := by
    intro hdiv
    have hf := simple_factor_survives 17 9 m (by norm_num) (by omega)
      (by decide +kernel) (by decide +kernel) hdiv
      (hlarge 17 (by norm_num) (by omega))
    have h17 : 17 ∣ Nat.fib m :=
      dvd_trans (by decide +kernel : 17 ∣ Nat.fib 9) (Nat.fib_dvd 9 m hdiv)
    exact hf (hpower.2 17 (by norm_num) h17)
  have h8 : ¬8 ∣ m := by
    intro hdiv
    have hf := simple_factor_survives 7 8 m (by norm_num) (by omega)
      (by decide +kernel) (by decide +kernel) hdiv
      (hlarge 7 (by norm_num) (by omega))
    have h7 : 7 ∣ Nat.fib m :=
      dvd_trans (by decide +kernel : 7 ∣ Nat.fib 8) (Nat.fib_dvd 8 m hdiv)
    exact hf (hpower.2 7 (by norm_num) h7)
  have hm12 : m ∣ 12 := by
    apply (Nat.factorization_prime_le_iff_dvd hm0 (by decide : (12 : ℕ) ≠ 0)).mp
    intro p hp
    by_cases hpm : p ∣ m
    · rcases small_prime_cases p hp (hsupport p hp hpm) with rfl | rfl | rfl
      · have hb : m.factorization 2 ≤ 2 := by
          by_contra h
          have hd := (Nat.prime_two.pow_dvd_iff_le_factorization hm0).mpr
            (show 3 ≤ m.factorization 2 by omega)
          exact h8 (by simpa using hd)
        exact hb.trans ((Nat.prime_two.pow_dvd_iff_le_factorization
          (by decide : (12 : ℕ) ≠ 0)).mp (by decide : 2 ^ 2 ∣ 12))
      · have hb : m.factorization 3 ≤ 1 := by
          by_contra h
          have hd := (Nat.prime_three.pow_dvd_iff_le_factorization hm0).mpr
            (show 2 ≤ m.factorization 3 by omega)
          exact h9 (by simpa using hd)
        exact hb.trans ((Nat.prime_three.pow_dvd_iff_le_factorization
          (by decide : (12 : ℕ) ≠ 0)).mp (by decide : 3 ^ 1 ∣ 12))
      · exact (h5 hpm).elim
    · have hz : m.factorization p = 0 := by
        by_contra h
        exact hpm (Nat.dvd_of_factorization_pos h)
      simp only [hz, Nat.zero_le]
  have hmle : m ≤ 12 := Nat.le_of_dvd (by omega) hm12
  have hcases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 12 := by
    interval_cases m <;> norm_num at hm hm12 ⊢
  rcases hcases with h | h | h | h | h | h
  · omega
  · omega
  · subst m
    have h := hpower.2 2 Nat.prime_two (by decide +kernel)
    norm_num [Nat.fib_add_two] at h
  · subst m
    have h := hpower.2 3 Nat.prime_three (by decide +kernel)
    norm_num [Nat.fib_add_two] at h
  · omega
  · omega

/-- A divisor of a prime-index Fibonacci value has that exact entry point. -/
private lemma prime_index_entry (ell p j : ℕ) (hell : ell.Prime)
    (hp : p.Prime) (hpf : p ∣ Nat.fib ell) (hpj : p ∣ Nat.fib j) : ell ∣ j := by
  by_contra hnot
  have hcop : ell.Coprime j := (hell.coprime_iff_not_dvd).mpr hnot
  have hg := Nat.dvd_gcd hpf hpj
  rw [← Nat.fib_gcd, hcop.gcd_eq_one, Nat.fib_one] at hg
  exact hp.not_dvd_one hg

/-- Every prime factor is larger than the prime index. The proof uses the
actual dev Frobenius/rank theorem, not an assumed bound on factor size. -/
private lemma prime_index_factor_large (ell p : ℕ) (hell : ell.Prime)
    (hell7 : 7 ≤ ell) (hp : p.Prime) (hpf : p ∣ Nat.fib ell) : ell < p := by
  have hell0 : 0 < ell := by omega
  have hp5 : p ≠ 5 := by
    intro heq
    subst p
    have hd := prime_index_entry ell 5 5 hell Nat.prime_five hpf (by decide +kernel)
    have := Nat.le_of_dvd (by omega : 0 < 5) hd
    omega
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    have hd := prime_index_entry ell 2 3 hell Nat.prime_two hpf (by decide +kernel)
    have := Nat.le_of_dvd (by omega : 0 < 3) hd
    omega
  have hmin : ∀ j : ℕ, 0 < j → p ∣ Nat.fib j → ell ≤ j := by
    intro j hj hdiv
    exact Nat.le_of_dvd hj (prime_index_entry ell p j hell hp hpf hdiv)
  have hb := fibonacci_rank_dvd_prime_bound hp hp5 hell0 hpf hmin
  by_cases heps : legendreSym 5 p = 1
  · rw [if_pos heps] at hb
    have hpge := hp.two_le
    have := Nat.le_of_dvd (by omega : 0 < p - 1) hb
    omega
  · rw [if_neg heps] at hb
    by_contra hnot
    have hple : p ≤ ell := by omega
    obtain ⟨k, hk⟩ := hb
    have hkpos : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      simp [hk0] at hk
    have hklt : k < 2 := by
      by_contra h
      have hmul := Nat.mul_le_mul_left ell (show 2 ≤ k by omega)
      omega
    have hk1 : k = 1 := by omega
    have heq : p + 1 = ell := by simpa only [hk1, Nat.mul_one] using hk
    obtain ⟨a, ha⟩ := hell.odd_of_ne_two (by omega)
    obtain ⟨b, hb⟩ := hp.odd_of_ne_two hp2
    omega

/-- A nonclassical powerful Fibonacci value has a powerful prime-index
block at the largest prime factor of its index. All value-primes of this
block lie beyond the index support and satisfy the standard p-square WSS
condition at their own signed Frobenius indices. -/
theorem powerful_fibonacci_counterexample_descends (m : ℕ) (hm : 0 < m)
    (hpower : Powerful (Nat.fib m))
    (hex : m ≠ 1 ∧ m ≠ 2 ∧ m ≠ 6 ∧ m ≠ 12) :
    ∃ ell : ℕ, ell.Prime ∧ 7 ≤ ell ∧ ell ∣ m ∧
      (∀ q : ℕ, q.Prime → q ∣ m → q ≤ ell) ∧
      Powerful (Nat.fib ell) ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.fib ell →
        ell < p ∧ p ^ 2 ∣ Nat.fib (if legendreSym 5 p = 1 then p - 1 else p + 1)) := by
  classical
  have hm0 : m ≠ 0 := by omega
  have hne : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  let ell := m.primeFactors.max' hne
  have hellmem : ell ∈ m.primeFactors := Finset.max'_mem _ _
  have hell : ell.Prime := Nat.prime_of_mem_primeFactors hellmem
  have helldvd : ell ∣ m := Nat.dvd_of_mem_primeFactors hellmem
  have hmax : ∀ q : ℕ, q.Prime → q ∣ m → q ≤ ell := by
    intro q hq hqm
    exact Finset.le_max' _ q (Nat.mem_primeFactors.mpr ⟨hq, hqm, hm0⟩)
  have hellbig : 5 < ell := by
    by_contra h
    have hs : ∀ q : ℕ, q.Prime → q ∣ m → q ≤ 5 := by
      intro q hq hqm
      exact (hmax q hq hqm).trans (by omega)
    have he := five_smooth_powerful m hm hs hpower
    omega
  have hell7 : 7 ≤ ell := by
    have h6 : ell ≠ 6 := by
      intro h
      have hprime : Nat.Prime 6 := h ▸ hell
      norm_num at hprime
    omega
  have hpell : Powerful (Nat.fib ell) := by
    refine ⟨by simpa only [Nat.fib_eq_zero] using (show ell ≠ 0 by omega), ?_⟩
    intro p hp hpf
    have hlp := prime_index_factor_large ell p hell hell7 hp hpf
    have hpm : ¬p ∣ m := by
      intro hdiv
      have := hmax p hp hdiv
      omega
    have hpfm : p ∣ Nat.fib m := hpf.trans (Nat.fib_dvd ell m helldvd)
    have hp2m := hpower.2 p hp hpfm
    obtain ⟨k, hk⟩ := helldvd
    rw [hk] at hp2m
    rcases (prime_square_fib_mul_iff p ell k hp (by omega) hpf).mp hp2m with h | h
    · exact h
    · exact (hpm (by rw [hk]; exact h.mul_left ell)).elim
  refine ⟨ell, hell, hell7, helldvd, hmax, hpell, ?_⟩
  intro p hp hpf
  have hlp := prime_index_factor_large ell p hell hell7 hp hpf
  have hmin : ∀ j : ℕ, 0 < j → p ∣ Nat.fib j → ell ≤ j := by
    intro j hj hdiv
    exact Nat.le_of_dvd hj (prime_index_entry ell p j hell hp hpf hdiv)
  have hb := fibonacci_rank_dvd_prime_bound hp (by omega : p ≠ 5)
    (by omega : 0 < ell) hpf hmin
  exact ⟨hlp, (hpell.2 p hp hpf).trans (Nat.fib_dvd _ _ hb)⟩

end D5.S3.Arith.FibonacciDepth.PowerfulPrimeDescent
