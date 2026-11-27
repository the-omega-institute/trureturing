/- GID: D5/S3/Arith/Recurrence/MandalMohanFibonacciPowerMean
   generality: I
   mirror-B: D5/B/S3/Arith/Recurrence/MandalMohanFibonacciPowerMean
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Fibonacci reciprocal-power quotients are integral exactly at prefix lengths 1 and 2. -/

import D5.S3.Arith.FibonacciRank
import OmegaBuild.Commands

/-! The integrality classification for the quotient in Conjecture 1.19. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset
open D5.S3.Arith.FibonacciRank

namespace D5.S3.Arith.Recurrence.MandalMohanFibonacciPowerMean

/-- The reciprocal sum over F₁ through Fₙ, with the summands in ℚ. -/
private def reciprocalSum (n k : ℕ) : ℚ :=
  ∑ i ∈ range n, 1 / (Nat.fib (i + 1) : ℚ) ^ k

private theorem reciprocalSum_pos {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    0 < reciprocalSum n k := by
  apply Finset.sum_pos'
  · intro i _
    positivity
  · exact ⟨0, Finset.mem_range.mpr (by omega), by simp⟩

private theorem two_le_reciprocalSum {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    2 ≤ reciprocalSum n k := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (s := range 2) (t := range n)
    (f := fun i => (1 : ℚ) / (Nat.fib (i + 1) : ℚ) ^ k)
    (Finset.range_mono hn) (by intros; positivity)
  norm_num [reciprocalSum, Finset.sum_range_succ] at h ⊢
  exact h

private theorem pow_dvd_of_clearing_denominators
    {s : Finset ℕ} {f b : ℕ → ℕ} {r p a q k e M : ℕ}
    (hr : r ∈ s) (hp : p.Prime) (hk : 0 < k)
    (hpos : ∀ i ∈ s, 0 < f i) (hscale : ∀ i ∈ s, M = f i * b i)
    (hpower : p ^ e ∣ M) (hrfree : ¬ p ∣ b r)
    (hothers : ∀ i ∈ s.erase r, p ∣ b i)
    (h : (a : ℚ) = (q : ℚ) * ∑ i ∈ s, 1 / (f i : ℚ) ^ k) :
    (p ^ e) ^ k ∣ q := by
  let B := ∑ i ∈ s, (b i) ^ k
  have hB : (B : ℚ) = (M : ℚ) ^ k * ∑ i ∈ s, 1 / (f i : ℚ) ^ k := by
    simp only [B, Nat.cast_sum, Finset.mul_sum, Nat.cast_pow]
    apply Finset.sum_congr rfl
    intro i hi
    have hfi : (f i : ℚ) ≠ 0 := by exact_mod_cast (hpos i hi).ne'
    rw [mul_one_div, eq_div_iff (pow_ne_zero k hfi), ← mul_pow, mul_comm]
    exact congrArg (fun x : ℚ => x ^ k) (by exact_mod_cast (hscale i hi).symm)
  have hcleared : a * M ^ k = q * B := by
    have heq : (a : ℚ) * (M : ℚ) ^ k = (q : ℚ) * (B : ℚ) := by
      rw [h, hB]
      ring
    exact_mod_cast heq
  have hBfree : ¬ p ∣ B := by
    intro hBdvd
    have hOther : p ∣ ∑ i ∈ s.erase r, (b i) ^ k :=
      Finset.dvd_sum fun i hi => (hothers i hi).trans (dvd_pow_self _ hk.ne')
    dsimp only [B] at hBdvd
    rw [← Finset.sum_erase_add s (fun i => (b i) ^ k) hr] at hBdvd
    exact hrfree (hp.dvd_of_dvd_pow ((Nat.dvd_add_iff_right hOther).mpr hBdvd))
  have hdvd : (p ^ e) ^ k ∣ q * B := by
    rw [← hcleared]
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpower k) a
  exact (hp.coprime_pow_of_not_dvd hBfree).symm.pow_left k |>.dvd_of_dvd_mul_right hdvd

/-- After clearing denominators, a prime dividing every summand except one
forces its full power in the common multiple into an integral quotient. -/
private theorem not_integral_of_cleared_denominators {n k p e r M : ℕ} {b : ℕ → ℕ}
    (hn : 2 ≤ n) (hk : 0 < k) (hp : p.Prime)
    (hr : r ∈ Finset.range n) (hbig : n ≤ p ^ e)
    (hpower : p ^ e ∣ M)
    (hscale : ∀ i ∈ Finset.range n, M = Nat.fib (i + 1) * b i)
    (hrfree : ¬ p ∣ b r)
    (hothers : ∀ i ∈ (Finset.range n).erase r, p ∣ b i) :
    ¬ ∃ q : ℕ, (n : ℚ) ^ k / reciprocalSum n k = (q : ℚ) := by
  rintro ⟨q, hq⟩
  have hsum := reciprocalSum_pos (by omega : 1 ≤ n) k
  have hqposRat : 0 < (q : ℚ) := by rw [← hq]; positivity
  have hqpos : 0 < q := by exact_mod_cast hqposRat
  have hqltRat : (q : ℚ) < (n : ℚ) ^ k := by
    rw [← hq]
    exact div_lt_self (by positivity) (by linarith [two_le_reciprocalSum hn k])
  have hqlt : q < n ^ k := by exact_mod_cast hqltRat
  have hnq : ((n ^ k : ℕ) : ℚ) = (q : ℚ) * reciprocalSum n k := by
    simpa using (div_eq_iff hsum.ne').mp hq
  have hdvd : (p ^ e) ^ k ∣ q :=
    pow_dvd_of_clearing_denominators (f := fun i => Nat.fib (i + 1)) hr hp hk
      (fun i _ => Nat.fib_pos.mpr (by omega)) hscale hpower hrfree hothers hnq
  exact (not_lt_of_ge ((Nat.pow_le_pow_left hbig k).trans (Nat.le_of_dvd hqpos hdvd))) hqlt

/-- A prime power in a single Fibonacci denominator excludes integrality when
that prime power is at least the prefix length. -/
private theorem not_integral_of_unique_prime_power {n k p e r : ℕ}
    (hn : 2 ≤ n) (hk : 0 < k) (he : 0 < e) (hp : p.Prime)
    (hr : r ∈ Finset.range n) (hbig : n ≤ p ^ e)
    (hpower : p ^ e ∣ Nat.fib (r + 1))
    (huniq : ∀ i ∈ (Finset.range n).erase r, ¬ p ∣ Nat.fib (i + 1)) :
    ¬ ∃ q : ℕ, (n : ℚ) ^ k / reciprocalSum n k = (q : ℚ) := by
  let f (i : ℕ) := Nat.fib (i + 1)
  let D := ∏ i ∈ (Finset.range n).erase r, f i
  let b : ℕ → ℕ := fun i => if i = r then D else f r * (D / f i)
  have hscale (i : ℕ) (hi : i ∈ Finset.range n) : f r * D = f i * b i := by
    by_cases hir : i = r
    · subst i
      simp [b]
    · have hdvd : f i ∣ D := Finset.dvd_prod_of_mem f (Finset.mem_erase.mpr ⟨hir, hi⟩)
      calc
        f r * D = f r * ((D / f i) * f i) := by rw [Nat.div_mul_cancel hdvd]
        _ = f i * b i := by simp only [b, ite_eq_right hir]; ac_rfl
  have hDfree : ¬ p ∣ D :=
    hp.coprime_iff_not_dvd.mp (Nat.Coprime.prod_right
      (fun i hi => hp.coprime_iff_not_dvd.mpr (huniq i hi)))
  have hpdvd : p ∣ f r := (dvd_pow_self _ he.ne').trans hpower
  refine not_integral_of_cleared_denominators hn hk hp hr hbig
    (dvd_mul_of_dvd_left hpower D) hscale ?_ ?_
  · simpa [b] using hDfree
  · intro i hi
    simp only [b, ite_eq_right (Finset.mem_erase.mp hi).1]
    exact dvd_mul_of_dvd_left hpdvd _

private theorem two_mul_dvd_of_odd_dvd_even {r m : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrm : r ∣ m) (hm : 2 ∣ m) :
    2 * r ∣ m := by
  have hcop : Nat.Coprime 2 r :=
    Nat.prime_two.coprime_iff_not_dvd.mpr (fun hd =>
      hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp hd).symm)
  exact hcop.mul_dvd_of_dvd_of_dvd hm hrm

/-- Bertrand supplies an index in the top half. A prime divisor of its Fibonacci
number has that index as its first zero, and lies beyond the prefix. -/
private theorem large_prime_witness {n : ℕ} (hn : 11 ≤ n) :
    ∃ r p : ℕ, (n + 1) / 2 < r ∧ r ≤ n ∧ r.Prime ∧ p.Prime ∧ n < p ∧
      p ∣ Nat.fib r ∧ ∀ j, 0 < j → j ≤ n → j ≠ r → ¬ p ∣ Nat.fib j := by
  obtain ⟨r, hr, hceil, hrle⟩ := Nat.exists_prime_lt_and_le_two_mul ((n + 1) / 2) (by omega)
  have hr5 : 5 < r := by omega
  have hrodd := hr.odd_of_ne_two (by omega : r ≠ 2)
  obtain ⟨u, hu⟩ := hrodd
  have hrn : r ≤ n := by omega
  have hFgt : 1 < Nat.fib r :=
    lt_of_lt_of_le (by decide : 1 < Nat.fib 3) (Nat.fib_mono (by omega))
  obtain ⟨p, hp, hpr⟩ := Nat.exists_prime_and_dvd hFgt.ne'
  have hrmin (j : ℕ) (hj : 0 < j) (hd : p ∣ Nat.fib j) : r ≤ j := by
    have hcommon := Nat.dvd_gcd hpr hd
    rw [← Nat.fib_gcd] at hcommon
    rcases (Nat.dvd_prime hr).mp (Nat.gcd_dvd_left r j) with h | h
    · rw [h, Nat.fib_one] at hcommon
      exact (hp.not_dvd_one hcommon).elim
    · exact h ▸ Nat.gcd_le_right r hj
  have hindex {j : ℕ} (hj : p ∣ Nat.fib j) : r ∣ j :=
    (fibonacci_entry_point hr.pos hpr hrmin).mp hj
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hrd := hindex (by decide : 2 ∣ Nat.fib 3)
    have := Nat.le_of_dvd (by decide : 0 < 3) hrd
    omega
  have hp5 : p ≠ 5 := by
    rintro rfl
    have hrd := hindex (by decide : 5 ∣ Nat.fib 5)
    have := Nat.le_of_dvd (by decide : 0 < 5) hrd
    omega
  have hbound := fibonacci_rank_dvd_prime_bound hp hp5 hr.pos hpr hrmin
  obtain ⟨v, hv⟩ := hp.odd_of_ne_two hp2
  have hpge := hp.two_le
  have hplt : n < p := by
    split at hbound
    · have h2p : 2 ∣ p - 1 := by use v; omega
      have h2r := two_mul_dvd_of_odd_dvd_even hr (by omega) hbound h2p
      have hle := Nat.le_of_dvd (by omega : 0 < p - 1) h2r
      omega
    · have h2p : 2 ∣ p + 1 := by use v + 1; omega
      have h2r := two_mul_dvd_of_odd_dvd_even hr (by omega) hbound h2p
      have hle := Nat.le_of_dvd (by omega : 0 < p + 1) h2r
      omega
  refine ⟨r, p, hceil, hrn, hr, hp, hplt, hpr, ?_⟩
  intro j hj hjn hjr hjp
  obtain ⟨m, hm⟩ := hindex hjp
  have hm2 : 2 ≤ m := by
    by_contra! h
    interval_cases m <;> simp_all
  have h2rj : 2 * r ≤ j := by
    rw [hm, Nat.mul_comm 2 r]
    exact Nat.mul_le_mul_left r hm2
  omega

private theorem three_not_integral {k : ℕ} (hk : 3 ≤ k) :
    ¬ ∃ q : ℕ, (3 : ℚ) ^ k / reciprocalSum 3 k = (q : ℚ) := by
  rintro ⟨q, hq⟩
  have hsum : reciprocalSum 3 k = 2 + 1 / (2 : ℚ) ^ k := by
    norm_num [reciprocalSum, Finset.sum_range_succ, show Nat.fib 3 = 2 by decide]
  rw [hsum] at hq
  have hq' := (div_eq_iff (by positivity)).mp hq
  have hcleared : (6 : ℚ) ^ k = (q : ℚ) * ((2 : ℚ) ^ (k + 1) + 1) := by
    calc
      (6 : ℚ) ^ k = (3 : ℚ) ^ k * (2 : ℚ) ^ k := by rw [← mul_pow]; norm_num
      _ = (q : ℚ) * ((2 : ℚ) ^ (k + 1) + 1) := by
        rw [hq', pow_succ]
        field_simp
  let d := 2 ^ (k + 1) + 1
  have hdvd : d ∣ 6 ^ k := by
    refine ⟨q, ?_⟩
    rw [mul_comm]
    exact_mod_cast hcleared
  have hd2 : ¬ 2 ∣ d := by
    have h2pow : 2 ∣ (2 : ℕ) ^ (k + 1) := dvd_pow_self _ (by omega)
    intro hd
    exact Nat.prime_two.not_dvd_one ((Nat.dvd_add_iff_right h2pow).mpr hd)
  rw [show (6 : ℕ) = 2 * 3 by decide, mul_pow] at hdvd
  have hd3 : d ∣ 3 ^ k :=
    ((Nat.prime_two.coprime_iff_not_dvd.mpr hd2).symm.pow_right k).dvd_of_dvd_mul_left hdvd
  obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd3
  have hbpos : 0 < b := by
    by_contra! hz
    have hzero : b = 0 := by omega
    simp [d, hzero] at hb
  have hmod : (3 : ZMod 8) ^ b = 1 := by
    have hcast := congrArg (fun a : ℕ => (a : ZMod 8)) hb
    push_cast [d] at hcast
    have hpow8 : (2 : ZMod 8) ^ (k + 1) = 0 := by
      rw [show k + 1 = 3 + (k - 2) by omega, pow_add]
      rw [show (2 : ZMod 8) ^ 3 = 0 by decide, zero_mul]
    simpa [hpow8] using hcast.symm
  obtain ⟨t, ht⟩ : ∃ t : ℕ, b = 2 * t := by
    rcases Nat.even_or_odd b with he | ho
    · obtain ⟨t, ht⟩ := he
      exact ⟨t, by omega⟩
    · obtain ⟨t, ht⟩ := ho
      rw [ht, pow_succ, pow_mul, show (3 : ZMod 8) ^ 2 = 1 by decide, one_pow, one_mul] at hmod
      exact (show (3 : ZMod 8) ≠ 1 by decide) hmod |>.elim
  have htpos : 0 < t := by omega
  let x := (3 : ℕ) ^ t
  have hx : 3 ≤ x := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 1 ≤ t)
  have hxsub : x - 1 + 1 = x := Nat.sub_add_cancel (by omega)
  have hxsq : x ^ 2 = 2 ^ (k + 1) + 1 := by
    rw [ht, Nat.mul_comm 2 t, pow_mul] at hb
    exact hb.symm
  have hfactor : (x - 1) * (x + 1) = 2 ^ (k + 1) := by
    nlinarith
  obtain ⟨a, _, ha⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp
      (hfactor ▸ (dvd_mul_right (x - 1) (x + 1)))
  obtain ⟨c, _, hc⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp
      (hfactor ▸ (dvd_mul_left (x + 1) (x - 1)))
  have ha1 : 1 ≤ a := by
    by_contra! hz
    have hzero : a = 0 := by omega
    simp [hzero] at ha
    omega
  have hac : a < c := by
    by_contra! hca
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hca
    omega
  have halt : a < 2 := by
    by_contra! ha2
    have ha4 : 4 ∣ x - 1 := by
      rw [ha]
      exact pow_dvd_pow _ ha2
    have hc4 : 4 ∣ x + 1 := by
      rw [hc]
      exact pow_dvd_pow _ (by omega : 2 ≤ c)
    omega
  have haeq : a = 1 := by omega
  rw [haeq, pow_one] at ha
  have h8 : 2 ^ (k + 1) = (2 : ℕ) ^ 3 := by
    rw [← hfactor, ha, show x + 1 = 4 by omega]
    decide
  have hkeq := pow_right_injective₀ (by decide : (0 : ℕ) < 2) (by decide : (2 : ℕ) ≠ 1) h8
  omega

private theorem four_not_integral {k : ℕ} (hk : 0 < k) :
    ¬ ∃ q : ℕ, (4 : ℚ) ^ k / reciprocalSum 4 k = (q : ℚ) := by
  rintro ⟨q, hq⟩
  have hsum : reciprocalSum 4 k = 2 + 1 / (2 : ℚ) ^ k + 1 / (3 : ℚ) ^ k := by
    norm_num [reciprocalSum, Finset.sum_range_succ, show Nat.fib 3 = 2 by decide,
      show Nat.fib 4 = 3 by decide]
  rw [hsum] at hq
  have hq' := (div_eq_iff (by positivity)).mp hq
  have hcleared : (24 : ℚ) ^ k = (q : ℚ) *
      (2 * (6 : ℚ) ^ k + (3 : ℚ) ^ k + (2 : ℚ) ^ k) := by
    calc
      (24 : ℚ) ^ k = (4 : ℚ) ^ k * ((2 : ℚ) ^ k * (3 : ℚ) ^ k) := by
        rw [← mul_pow, ← mul_pow]
        norm_num
      _ = (q : ℚ) * (2 * (6 : ℚ) ^ k + (3 : ℚ) ^ k + (2 : ℚ) ^ k) := by
        rw [hq', show (6 : ℚ) = 2 * 3 by norm_num, mul_pow]
        field_simp
  let d := 2 * 6 ^ k + 3 ^ k + 2 ^ k
  have hdvd : d ∣ 24 ^ k := by
    refine ⟨q, ?_⟩
    rw [mul_comm]
    exact_mod_cast hcleared
  have hd2 : ¬ 2 ∣ d := by
    intro hd
    have hright : 2 ∣ (2 : ℕ) ^ k := dvd_pow_self _ hk.ne'
    have hleft : 2 ∣ 2 * (6 : ℕ) ^ k := dvd_mul_right _ _
    have h := (Nat.dvd_add_iff_right hleft).mpr ((Nat.dvd_add_iff_left hright).mpr hd)
    exact (by decide : ¬ 2 ∣ 3) (Nat.prime_two.dvd_of_dvd_pow h)
  have hd3 : ¬ 3 ∣ d := by
    intro hd
    have h6 : 3 ∣ (6 : ℕ) ^ k :=
      dvd_trans (by decide : 3 ∣ 6) (dvd_pow_self _ hk.ne')
    have hleft : 3 ∣ 2 * (6 : ℕ) ^ k + (3 : ℕ) ^ k :=
      dvd_add (dvd_mul_of_dvd_right h6 _) (dvd_pow_self _ hk.ne')
    exact (by decide : ¬ 3 ∣ 2)
      (Nat.prime_three.dvd_of_dvd_pow ((Nat.dvd_add_iff_right hleft).mpr hd))
  have hc2 := (Nat.prime_two.coprime_iff_not_dvd.mpr hd2).symm
  have hc3 := (Nat.prime_three.coprime_iff_not_dvd.mpr hd3).symm
  have hc24 : Nat.Coprime d 24 := (hc2.pow_right 3).mul_right hc3
  have hone := Nat.eq_one_of_dvd_coprimes (hc24.pow_right k) (dvd_refl d) hdvd
  have hdpos : 1 < d := by
    have h6pos : 0 < (6 : ℕ) ^ k := by positivity
    calc
      1 < 2 * (6 : ℕ) ^ k := by omega
      _ ≤ d := by
        exact (Nat.le_add_right (2 * 6 ^ k) (3 ^ k)).trans (Nat.le_add_right _ _)
  omega

private theorem small_witness_not_integral {n k : ℕ} (hn5 : 5 ≤ n) (hn10 : n ≤ 10)
    (hk : 0 < k) :
    ¬ ∃ q : ℕ, (n : ℚ) ^ k / reciprocalSum n k = (q : ℚ) := by
  rcases eq_or_lt_of_le hn5 with rfl | hn5
  · refine not_integral_of_unique_prime_power (p := 5) (e := 1) (r := 4)
      (by decide) hk (by decide) (by decide) (by decide) (by decide) (by decide) ?_
    intro j hj
    have htest : ∀ i : Fin 5, i.val ≠ 4 → ¬ 5 ∣ Nat.fib (i.val + 1) := by decide
    have ⟨hne, hlt⟩ := Finset.mem_erase.mp hj
    exact htest ⟨j, Finset.mem_range.mp hlt⟩ hne
  rcases eq_or_lt_of_le (by omega : 6 ≤ n) with rfl | hn6
  · let b : ℕ → ℕ := fun i => 120 / Nat.fib (i + 1)
    refine not_integral_of_cleared_denominators (p := 2) (e := 3) (r := 5)
      (M := 120) (b := b) (by decide) hk (by decide) (by decide) (by decide)
      (by decide) ?_ (by decide) ?_
    · intro i hi
      have htest : ∀ j : Fin 6, 120 = Nat.fib (j.val + 1) * b j.val := by decide
      exact htest ⟨i, Finset.mem_range.mp hi⟩
    · intro i hi
      have htest : ∀ j : Fin 6, j.val ≠ 5 → 2 ∣ b j.val := by decide
      have ⟨hne, hlt⟩ := Finset.mem_erase.mp hi
      exact htest ⟨i, Finset.mem_range.mp hlt⟩ hne
  · refine not_integral_of_unique_prime_power (p := 13) (e := 1) (r := 6) (by omega) hk
      (by decide) (by decide) (Finset.mem_range.mpr (by omega)) (by simp; omega) (by decide) ?_
    intro j hj
    have htest : ∀ i : Fin 10, i.val ≠ 6 → ¬ 13 ∣ Nat.fib (i.val + 1) := by decide
    have ⟨hne, hlt⟩ := Finset.mem_erase.mp hj
    exact htest ⟨j, (Finset.mem_range.mp hlt).trans_le hn10⟩ hne

private theorem conjecture_range (n k : ℕ) (hn : 1 ≤ n) (hk : 3 ≤ k) :
    (∃ q : ℕ, (n : ℚ) ^ k / reciprocalSum n k = (q : ℚ)) ↔ n = 1 ∨ n = 2 := by
  constructor
  · intro h
    by_cases h1 : n = 1
    · exact Or.inl h1
    by_cases h2 : n = 2
    · exact Or.inr h2
    exfalso
    by_cases h3 : n = 3
    · subst n
      exact three_not_integral hk h
    by_cases h4 : n = 4
    · subst n
      exact four_not_integral (by omega) h
    by_cases h10 : n ≤ 10
    · exact small_witness_not_integral (by omega) h10 (by omega) h
    obtain ⟨r, p, _, hrn, hr, hp, hnp, hd, huniq⟩ := large_prime_witness (by omega : 11 ≤ n)
    have hindex : r - 1 + 1 = r := Nat.sub_add_cancel hr.one_le
    refine not_integral_of_unique_prime_power (p := p) (e := 1) (r := r - 1)
      (by omega) (by omega) (by decide) hp (Finset.mem_range.mpr (by omega))
      (by simpa using hnp.le) (by simpa [hindex] using hd) ?_ h
    intro i hi
    obtain ⟨hir, hin⟩ := Finset.mem_erase.mp hi
    have hin' := Finset.mem_range.mp hin
    exact huniq (i + 1) (by omega) (by omega) (by omega)
  · rintro (rfl | rfl)
    · refine ⟨1, ?_⟩
      simp [reciprocalSum]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      refine ⟨2 ^ m, ?_⟩
      rw [show reciprocalSum 2 (m + 1) = 2 by norm_num [reciprocalSum, Finset.sum_range_succ]]
      push_cast
      rw [pow_succ]
      field_simp

/-- The rational expression in Mandal and Mohan's Conjecture 1.19. -/
def quotient (k n : ℕ) : ℚ :=
  (n : ℚ) ^ k / (∑ i ∈ Finset.Icc 1 n, 1 / (Nat.fib i : ℚ) ^ k)

/-- Conjecture 1.19 of arXiv:2611.32519v1, with the nonempty prefix made explicit. -/
def claim : Prop :=
  ∀ n k : ℕ, 1 ≤ n → 3 ≤ k →
    ((∃ q : ℕ, quotient k n = (q : ℚ)) ↔ n = 1 ∨ n = 2)

/-- The conjecture holds in the full published range. -/
theorem result : claim := by
  intro n k hn hk
  have hsum :
      (∑ i ∈ Finset.Icc 1 n, 1 / (Nat.fib i : ℚ) ^ k) = reciprocalSum n k := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [reciprocalSum, add_comm]
  simpa only [quotient, hsum] using conjecture_range n k hn hk

end D5.S3.Arith.Recurrence.MandalMohanFibonacciPowerMean
