/- GID: D5/S3/Arith/Primes/GoldenCubicFiveClock
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicFiveClock
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Every native five-adic Lucas block collision is an exact signed-order return, with no transient. -/

import D5.S3.Arith.Primes.FibonacciFiveAdicDepth
import D5.S3.Arith.Primes.GoldenCubicBlockFibonacciLagProduct
import D5.S3.Arith.Primes.GoldenCubicSignedOrder

set_option autoImplicit false

namespace D5.S3.Arith.Primes.GoldenCubicFiveClock

open D5.S1.Scale GoldenCubicSignedOrder
open GoldenCubicBlockFibonacciLagProduct FibonacciFiveAdicDepth

private theorem cube_indices_five_product (n m : ℕ) (hmn : m < n) :
    ((3:ℕ)^n+3^m)*(3^n-3^m) = 9^m*(9^(n-m)-1) := by
  have hmul : (3:ℕ)^n = 3^m*3^(n-m) := by rw [← pow_add, Nat.add_sub_of_le hmn.le]
  have hsum : (3:ℕ)^n + 3^m = 3^m*(3^(n-m)+1) := by rw [hmul]; ring
  have hdiff : (3:ℕ)^n - 3^m = 3^m*(3^(n-m)-1) := by rw [hmul, Nat.mul_sub, mul_one]
  rw [hsum, hdiff]
  have hmul' (x : ℕ) (hx : 1 ≤ x) : (x+1)*(x-1) = x^2-1 := by
    have hx' : 1 ≤ x^2 := Nat.one_le_pow _ _ hx
    zify [hx,hx']
    ring
  calc
    _ = ((3:ℕ)^m)^2 * (((3:ℕ)^(n-m)+1)*((3:ℕ)^(n-m)-1)) := by ring
    _ = _ := by
      rw [hmul' _ (Nat.one_le_pow _ _ (by decide)), ← pow_mul, ← pow_mul,
        Nat.mul_comm m 2, Nat.mul_comm (n-m) 2, pow_mul, pow_mul, show (3:ℕ)^2=9 by decide]

/-- The exact native five-adic lag is one extra factor from the golden
discriminant, plus the lag valuation of a power of nine minus one. -/
theorem cubicBlock_five_lag (n m : ℕ) (hmn : m < n) :
    padicValInt 5 ((goldenLucas (3^n)^2+3)-(goldenLucas (3^m)^2+3)) =
      1+padicValNat 5 (9^(n-m)-1) := by
  let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hpow : (3:ℕ)^m < 3^n := Nat.pow_lt_pow_right (by decide) hmn
  have hA : 0 < (3:ℕ)^n+3^m := by positivity
  have hD : 0 < (3:ℕ)^n-3^m := Nat.sub_pos_of_lt hpow
  have hfA : (Nat.fib (3^n+3^m):ℤ) ≠ 0 := by exact_mod_cast (Nat.fib_pos.mpr hA).ne'
  have hfD : (Nat.fib (3^n-3^m):ℤ) ≠ 0 := by exact_mod_cast (Nat.fib_pos.mpr hD).ne'
  have hd : 9^(n-m)-1 ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt (one_lt_pow₀ (by decide) (by omega)))
  have hpow5 : padicValNat 5 ((9:ℕ)^m) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    exact fun H => (by decide : ¬ 5 ∣ 9) (Nat.prime_five.dvd_of_dvd_pow H)
  have hfive : padicValInt 5 (5:ℤ) = 1 := padicValInt_self
  rw [cubic_block_fibonacci_lag_product n m hmn.le,
    padicValInt.mul (mul_ne_zero (by decide) hfA) hfD,
    padicValInt.mul (by decide) hfA, padicValInt.of_nat, padicValInt.of_nat,
    hfive, fibonacci_five_adic_depth _ hA, fibonacci_five_adic_depth _ hD, add_assoc,
    ← padicValNat.mul hA.ne' hD.ne', cube_indices_five_product n m hmn,
    padicValNat.mul (by positivity) hd, hpow5, zero_add]

/-- There is no five-adic transient: every native collision, even when
the earlier index is zero, is exactly a signed-order lag. -/
theorem cubicBlock_five_collision (a n m : ℕ) (hmn : m < n) :
    (goldenLucas (3^n)^2+3) ≡ (goldenLucas (3^m)^2+3) [ZMOD (5:ℤ)^a] ↔
      signedOrder 3 (5^(a-1)) ((by decide : (3:ℕ).Coprime 5).pow_right (a-1)) ∣ n-m := by
  let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hv := cubicBlock_five_lag n m hmn
  have hD : (goldenLucas (3^n)^2+3)-(goldenLucas (3^m)^2+3) ≠ 0 := by
    intro H
    rw [H, padicValInt.zero] at hv
    omega
  have hpow : 1 < (9:ℕ)^(n-m) := one_lt_pow₀ (by decide) (by omega)
  have hd : 9^(n-m)-1 ≠ 0 := (Nat.sub_pos_of_lt hpow).ne'
  have hV := padicValInt_dvd_iff_of_ne_one (by decide : (5:ℕ) ≠ 1) a
    ((goldenLucas (3^n)^2+3)-(goldenLucas (3^m)^2+3))
  norm_num only [Nat.cast_ofNat] at hV
  rw [Int.modEq_iff_dvd, ← Int.dvd_neg,
    show -((goldenLucas (3^m)^2+3)-(goldenLucas (3^n)^2+3)) =
      (goldenLucas (3^n)^2+3)-(goldenLucas (3^m)^2+3) by ring, hV, or_iff_right hD, hv,
    three_signedOrder_prime_power 5 _ Nat.prime_five (by decide),
    orderOf_dvd_iff_pow_eq_one]
  have ht : ((9:ZMod (5^(a-1)))^(n-m) = 1) ↔ (5:ℕ)^(a-1) ∣ 9^(n-m)-1 := by
    have H := (ZMod.natCast_eq_natCast_iff (9^(n-m)) 1 (5^(a-1))).trans
      (Iff.trans Nat.ModEq.comm (Nat.modEq_iff_dvd' hpow.le))
    simpa only [Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] using H
  rw [ht, padicValNat_dvd_iff_le hd]
  omega

theorem cubicBlock_five_collision_explicit (a n m : ℕ) (hmn : m < n) :
    (goldenLucas (3^n)^2+3) ≡ (goldenLucas (3^m)^2+3) [ZMOD (5:ℤ)^a] ↔
      (if a ≤ 1 then 1 else 2*5^(a-2)) ∣ n-m := by
  rw [cubicBlock_five_collision a n m hmn, signedOrder_three_mod_five_pow]
  have ha : a-1=0 ↔ a≤1 := by omega
  simp only [ha, Nat.sub_sub, show (1:ℕ)+1=2 by decide]

end D5.S3.Arith.Primes.GoldenCubicFiveClock
