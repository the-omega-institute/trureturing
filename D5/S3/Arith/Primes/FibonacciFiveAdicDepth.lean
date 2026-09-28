/- GID: D5/S3/Arith/Primes/FibonacciFiveAdicDepth
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciFiveAdicDepth
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The five-adic valuation of a positive-index Fibonacci number equals that of its index. -/

import D5.S1.Scale.Lucas
import D5.S3.Arith.FibonacciRank
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.FibonacciFiveAdicDepth

open D5.S0.Carrier D5.S1.Scale

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The ramified prime has exactly the same depth in a positive Fibonacci
number as in its index. The proof computes the fifth golden power and shows
that its residual coordinate factor is a unit modulo five. -/
theorem fibonacci_five_adic_depth (n : ℕ) (hn : 0 < n) :
    padicValNat 5 (Nat.fib n) = padicValNat 5 n := by
  let Q (a b : ℤ) : ℤ := a ^ 4 + 2 * a ^ 3 * b + 4 * a ^ 2 * b ^ 2 +
    3 * a * b ^ 3 + b ^ 4
  have hstep (m : ℕ) (hm : 0 < m) :
      padicValNat 5 (Nat.fib (5 * m)) = padicValNat 5 (Nat.fib m) + 1 := by
    let x : GoldenInt := phi ^ m
    have hb : x.b = (Nat.fib m : ℤ) := by
      simpa [x] using golden_phi_pow_b_eq_fib_index m
    have hbne : x.b ≠ 0 := by
      rw [hb]
      exact_mod_cast (Nat.fib_pos.mpr hm).ne'
    have hb5 : (x ^ 5).b = (Nat.fib (5 * m) : ℤ) := by
      simpa [x, ← pow_mul, Nat.mul_comm] using
        golden_phi_pow_b_eq_fib_index (5 * m)
    have hpoly : (x ^ 5).b = 5 * x.b * Q x.a x.b := by
      simp only [pow_succ, pow_zero, one_mul, a_mul, b_mul, Q]
      ring
    have hnorm : x.a * x.a + x.a * x.b - x.b * x.b = (-1 : ℤ) ^ m := by
      have h := norm_phi_pow m
      change x.a * x.a + x.a * x.b - x.b * x.b = (-1 : ℤ) ^ m at h
      exact h
    have hnorm5 : (x.a : ZMod 5) * (x.a : ZMod 5) +
        (x.a : ZMod 5) * (x.b : ZMod 5) -
        (x.b : ZMod 5) * (x.b : ZMod 5) = (-1 : ZMod 5) ^ m := by
      have h := congrArg (fun z : ℤ => (z : ZMod 5)) hnorm
      push_cast at h
      exact h
    have hu : (x.a : ZMod 5) + 3 * (x.b : ZMod 5) ≠ 0 := by
      intro hz
      have ha : (x.a : ZMod 5) = -3 * (x.b : ZMod 5) := by
        linear_combination hz
      have hnzero : (x.a : ZMod 5) * (x.a : ZMod 5) +
          (x.a : ZMod 5) * (x.b : ZMod 5) -
          (x.b : ZMod 5) * (x.b : ZMod 5) = 0 := by
        rw [ha]
        ring_nf
        have hfive : (5 : ZMod 5) = 0 := by decide
        simp [hfive]
      rw [hnzero] at hnorm5
      exact (pow_ne_zero m (by norm_num : (-1 : ZMod 5) ≠ 0)) hnorm5.symm
    have hQcast : (Q x.a x.b : ZMod 5) =
        ((x.a : ZMod 5) + 3 * (x.b : ZMod 5)) ^ 4 := by
      dsimp [Q]
      push_cast
      ring_nf
      simp only [show (108 : ZMod 5) = 3 by decide,
        show (54 : ZMod 5) = 4 by decide,
        show (12 : ZMod 5) = 2 by decide,
        show (81 : ZMod 5) = 1 by decide, mul_one]
    have hQnot : ¬(5 : ℤ) ∣ Q x.a x.b := by
      intro hd
      have hz : (Q x.a x.b : ZMod 5) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr hd
      rw [hQcast] at hz
      exact (pow_ne_zero 4 hu) hz
    have hQne : Q x.a x.b ≠ 0 := by
      intro hz
      exact hQnot (hz ▸ dvd_zero _)
    have hval : padicValInt 5 (x ^ 5).b = padicValInt 5 x.b + 1 := by
      rw [hpoly, padicValInt.mul (mul_ne_zero (by decide : (5 : ℤ) ≠ 0) hbne) hQne,
        padicValInt.mul (by decide : (5 : ℤ) ≠ 0) hbne]
      have hval5 : padicValInt 5 (5 : ℤ) = 1 := padicValInt.self (by decide)
      rw [hval5, padicValInt.eq_zero_of_not_dvd hQnot]
      omega
    rw [hb5, hb] at hval
    simpa only [padicValInt.of_nat] using hval
  have hentry (k : ℕ) : 5 ∣ Nat.fib k ↔ 5 ∣ k := by
    have hmin : ∀ j : ℕ, 0 < j → 5 ∣ Nat.fib j → 5 ≤ j := by
      intro j hj hdiv
      by_contra hlt
      have hjlt : j ≤ 4 := by omega
      interval_cases j <;> norm_num [Nat.fib] at hdiv
    exact D5.S3.Arith.FibonacciRank.fibonacci_entry_point
      (p := 5) (k := 5) (n := k) (by decide) (by norm_num [Nat.fib]) hmin
  have hmain : ∀ k : ℕ, 0 < k →
      padicValNat 5 (Nat.fib k) = padicValNat 5 k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        by_cases h5 : 5 ∣ k
        · obtain ⟨m, rfl⟩ := h5
          have hm : 0 < m := by omega
          have hlt : m < 5 * m := by omega
          rw [hstep m hm, ih m hlt hm]
          rw [padicValNat.mul (by decide : (5 : ℕ) ≠ 0) hm.ne', padicValNat_self]
          omega
        · have hFib5 : ¬5 ∣ Nat.fib k := by
            intro h
            exact h5 ((hentry k).mp h)
          rw [padicValNat.eq_zero_of_not_dvd hFib5,
            padicValNat.eq_zero_of_not_dvd h5]
  exact hmain n hn

#print axioms fibonacci_five_adic_depth

end D5.S3.Arith.Primes.FibonacciFiveAdicDepth
