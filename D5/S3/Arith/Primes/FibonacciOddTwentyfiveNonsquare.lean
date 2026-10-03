/- GID: D5/S3/Arith/Primes/FibonacciOddTwentyfiveNonsquare
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciOddTwentyfiveNonsquare
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Odd-index normalized Fibonacci quotients have nonsquare residue five modulo seven. -/

import D5.S3.Arith.Primes.FibonacciFiveAdicDepth
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.FibonacciOddTwentyfiveNonsquare

/-- After the exact factor of twenty-five is removed, every positive
odd-index twenty-five-fold Fibonacci quotient is five modulo seven. -/
theorem fibonacci_odd_twentyfive_normalized_nonsquare
    (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    ∃ d : ℕ, Nat.fib (25 * n) = 25 * Nat.fib n * d ∧
      (d : ZMod 7) = 5 ∧ ¬ IsSquare d := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hshift (r : ℕ) :
      (Nat.fib (r + 8) : ZMod 7) = -(Nat.fib r : ZMod 7) := by
    have h := Nat.fib_add 7 r
    have heq : 7 + r + 1 = r + 8 := by omega
    rw [heq] at h
    have hf7 : Nat.fib 7 = 13 := by decide
    rw [hf7] at h
    norm_num only at h
    have hc : (Nat.fib (r + 8) : ZMod 7) =
        (13 : ZMod 7) * Nat.fib r + (21 : ZMod 7) * Nat.fib (r + 1) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        congrArg (fun x : ℕ => (x : ZMod 7)) h
    have h13 : (13 : ZMod 7) = -1 := by decide
    have h21 : (21 : ZMod 7) = 0 := by decide
    simpa only [h13, h21, zero_mul, add_zero, neg_mul, one_mul] using hc
  have hshiftMul (r k : ℕ) :
      (Nat.fib (r + 8 * k) : ZMod 7) = (-1 : ZMod 7) ^ k * Nat.fib r := by
    induction k with
    | zero => simp
    | succ k ih =>
        have hs := hshift (r + 8 * k)
        have heq : r + 8 * (k + 1) = (r + 8 * k) + 8 := by omega
        rw [heq, hs, ih, pow_succ]
        ring
  have hmod : (Nat.fib (25 * n) : ZMod 7) = -(Nat.fib n : ZMod 7) := by
    have hs := hshiftMul n (3 * n)
    have heq : n + 8 * (3 * n) = 25 * n := by omega
    rw [heq] at hs
    have h3odd : Odd (3 * n) := (by decide : Odd (3 : ℕ)).mul hodd
    rw [h3odd.neg_one_pow] at hs
    simpa only [neg_mul, one_mul] using hs
  have hnonzero : (Nat.fib n : ZMod 7) ≠ 0 := by
    have hentry (m : ℕ) : 7 ∣ Nat.fib m ↔ 8 ∣ m := by
      apply D5.S3.Arith.FibonacciRank.fibonacci_entry_point
        (by decide : 0 < 8) (by decide : 7 ∣ Nat.fib 8)
      intro j hj hdiv
      by_contra hlt
      have hjle : j ≤ 7 := by omega
      interval_cases j <;> norm_num [Nat.fib] at hdiv
    intro hz
    have hdiv : 8 ∣ n := (hentry n).mp ((ZMod.natCast_eq_zero_iff _ _).mp hz)
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨m, hm⟩ := hdiv
    omega
  let R := Nat.fib (25 * n) / Nat.fib n
  have hFnpos : 0 < Nat.fib n := Nat.fib_pos.mpr hn
  have hF25pos : 0 < Nat.fib (25 * n) := Nat.fib_pos.mpr (by omega)
  have hdiv : Nat.fib n ∣ Nat.fib (25 * n) :=
    Nat.fib_dvd n (25 * n) ⟨25, by omega⟩
  have hmul : Nat.fib n * R = Nat.fib (25 * n) := Nat.mul_div_cancel' hdiv
  have hRpos : 0 < R := Nat.div_pos (Nat.le_of_dvd hF25pos hdiv) hFnpos
  have hval : padicValNat 5 (Nat.fib (25 * n)) =
      padicValNat 5 (Nat.fib n) + padicValNat 5 R := by
    rw [← hmul]
    exact padicValNat.mul hFnpos.ne' hRpos.ne'
  have hindex : padicValNat 5 (25 * n) = padicValNat 5 n + 2 := by
    rw [show (25 : ℕ) = 5 ^ 2 by norm_num,
      padicValNat.mul (by decide : 5 ^ 2 ≠ 0) hn.ne',
      padicValNat.pow, padicValNat_self]
    omega
  rw [D5.S3.Arith.Primes.FibonacciFiveAdicDepth.fibonacci_five_adic_depth
    (25 * n) (by omega),
    D5.S3.Arith.Primes.FibonacciFiveAdicDepth.fibonacci_five_adic_depth n hn,
    hindex] at hval
  have h25div : 25 ∣ R := by
    have hpow : 5 ^ 2 ∣ R :=
      (padicValNat_dvd_iff_le hRpos.ne').mpr (by omega)
    simpa using hpow
  obtain ⟨d, hd⟩ := h25div
  have hmain : Nat.fib (25 * n) = 25 * Nat.fib n * d := by
    rw [← hmul, hd]
    ring
  have hc : (Nat.fib (25 * n) : ZMod 7) =
      (25 : ZMod 7) * Nat.fib n * d := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun x : ℕ => (x : ZMod 7)) hmain
  have h255 : (25 : ZMod 7) * 5 = -1 := by decide
  have hfactor : ((25 : ZMod 7) * Nat.fib n) * (d : ZMod 7) =
      ((25 : ZMod 7) * Nat.fib n) * 5 := by
    calc
      _ = -(Nat.fib n : ZMod 7) := hc.symm.trans hmod
      _ = ((25 : ZMod 7) * Nat.fib n) * 5 := by
        rw [mul_right_comm, h255]
        ring
  have h25ne : (25 : ZMod 7) ≠ 0 := by decide
  have hdmod : (d : ZMod 7) = 5 :=
    mul_left_cancel₀ (mul_ne_zero h25ne hnonzero) hfactor
  have hnonsq : ¬ IsSquare d := by
    intro hs
    have hs7 : IsSquare (d : ZMod 7) := hs.map (Nat.castRingHom (ZMod 7))
    rw [hdmod] at hs7
    exact (by decide : ¬ IsSquare (5 : ZMod 7)) hs7
  exact ⟨d, hmain, hdmod, hnonsq⟩

#print axioms fibonacci_odd_twentyfive_normalized_nonsquare

end D5.S3.Arith.Primes.FibonacciOddTwentyfiveNonsquare
