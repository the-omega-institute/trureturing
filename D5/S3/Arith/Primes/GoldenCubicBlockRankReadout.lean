/- GID: D5/S3/Arith/Primes/GoldenCubicBlockRankReadout
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicBlockRankReadout
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Fibonacci entry ranks determine the odd-prime depths of every native cubic Lucas lag. -/

import D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation

import D5.S3.Arith.Primes.FibonacciPrimeStepLift
import D5.S3.Arith.Primes.GoldenCubicBlockFibonacciLagProduct
import D5.S3.Arith.Primes.GoldenCubicDyadicClock

set_option autoImplicit false

/-! Exact Fibonacci entry-rank and all-prime Lucas lag valuations. -/

namespace D5.S3.Arith.Primes.GoldenCubicBlockRankReadout
open D5.S1.Scale FiniteFibonacciRankClosure FibonacciPrimeToIndexValuation

/-- The only missing arithmetic ingredient is the exact valuation gain
when multiplying a positive Fibonacci zero index by one copy of p. -/
def OneStep (p : ℕ) : Prop :=
  ∀ r : ℕ, 0 < r → p ∣ Nat.fib r →
    padicValNat p (Nat.fib (r*p)) = padicValNat p (Nat.fib r)+1

theorem valuation_pow_mul (p r e : ℕ) (h : OneStep p)
    (hr : 0 < r) (hpr : p ∣ Nat.fib r) (hp : p.Prime) :
    padicValNat p (Nat.fib (r*p^e)) = padicValNat p (Nat.fib r)+e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hr' : 0 < r*p^e := mul_pos hr (pow_pos hp.pos _)
    have hd : p ∣ Nat.fib (r*p^e) := hpr.trans
      (Nat.fib_dvd _ _ (dvd_mul_right _ _))
    rw [pow_succ, ← Nat.mul_assoc, h _ hr' hd, ih, Nat.add_assoc]

theorem valuation_mul (p r k : ℕ) (hp : p.Prime) (h : OneStep p)
    (hr : 0 < r) (hpr : p ∣ Nat.fib r) (hk : k ≠ 0) :
    padicValNat p (Nat.fib (r*k)) = padicValNat p (Nat.fib r)+padicValNat p k := by
  let _ : Fact p.Prime := ⟨hp⟩
  let e := padicValNat p k
  let q := k.divMaxPow p
  have he : p^e*q = k := Nat.pow_padicValNat_mul_divMaxPow p k
  have hq : ¬ p ∣ q := Nat.not_dvd_divMaxPow hp.one_lt hk
  have hr' : 0 < r*p^e := mul_pos hr (pow_pos hp.pos _)
  have hd : p ∣ Nat.fib (r*p^e) := hpr.trans
    (Nat.fib_dvd _ _ (dvd_mul_right _ _))
  calc
    padicValNat p (Nat.fib (r*k)) =
        padicValNat p (Nat.fib ((r*p^e)*q)) := by rw [Nat.mul_assoc, he]
    _ = padicValNat p (Nat.fib (r*p^e)) := fibonacci_valuation_stable p _ _ hp hr' hd hq
    _ = _ := valuation_pow_mul p r e h hr hpr hp

theorem entry_rank_div_iff (p n : ℕ) (hp : p.Prime) :
    p ∣ Nat.fib n ↔ fibonacciRank p ∣ n := by
  have h := (rankWitness p hp).property
  simpa only [fibonacciRank, dite_eq_left hp] using
    (D5.S3.Arith.FibonacciRank.fibonacci_entry_point (n := n) h.1 h.2.1 h.2.2)

theorem valuation_by_rank (p n : ℕ) (hp : p.Prime) (h : OneStep p) (hn : 0 < n) :
    padicValNat p (Nat.fib n) =
      if fibonacciRank p ∣ n then padicValNat p (Nat.fib (fibonacciRank p))+
        padicValNat p (n / fibonacciRank p) else 0 := by
  split_ifs with hd
  · have he : fibonacciRank p*(n/fibonacciRank p) = n := Nat.mul_div_cancel' hd
    have hz : n/fibonacciRank p ≠ 0 := by
      intro he'
      rw [he', mul_zero] at he
      omega
    have hr' : 0 < fibonacciRank p := by
      simpa only [fibonacciRank, dite_eq_left hp] using (rankWitness p hp).property.1
    have hd' : p ∣ Nat.fib (fibonacciRank p) := (entry_rank_div_iff p _ hp).mpr dvd_rfl
    conv_lhs => rw [← he]
    exact valuation_mul p _ _ hp h hr' hd' hz
  · exact padicValNat.eq_zero_of_not_dvd (fun x => hd ((entry_rank_div_iff p _ hp).mp x))

/-- The rank hit, its first-entry depth, and the additional p-divisibility
of the quotient give the full valuation of the Fibonacci value for odd p. -/
def valuationReadout (p n : ℕ) : ℕ :=
  if fibonacciRank p ∣ n then padicValNat p (Nat.fib (fibonacciRank p)) +
    padicValNat p (n/fibonacciRank p) else 0

theorem valuation_eq_readout (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n) :
    padicValNat p (Nat.fib n) = valuationReadout p n := by
  apply valuation_by_rank p n hp _ hn
  intro r hr hd
  simpa only [Nat.mul_comm, Nat.add_comm] using
    FibonacciPrimeStepLift.fibonacci_valuation_prime_step p r hp hp2 hr hd

/-- No witness divisor assumption: every odd-prime residue collision
on the actual Lucas trajectory has an exact Fibonacci-rank readout. -/
theorem cubic_block_odd_prime_rank_lag (p n m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hmn : m < n) :
    padicValInt p ((goldenLucas (3^n)^2+3)-(goldenLucas (3^m)^2+3)) =
      (if p=5 then 1 else 0) + valuationReadout p (3^n+3^m) +
        valuationReadout p (3^n-3^m) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hpow : (3:ℕ)^m < 3^n := Nat.pow_lt_pow_right (by decide) hmn
  have ha : 0 < (3:ℕ)^n+3^m := by positivity
  have hb : 0 < (3:ℕ)^n-3^m := Nat.sub_pos_of_lt hpow
  have hfa : (Nat.fib (3^n+3^m):ℤ) ≠ 0 := by exact_mod_cast (Nat.fib_pos.mpr ha).ne'
  have hfb : (Nat.fib (3^n-3^m):ℤ) ≠ 0 := by exact_mod_cast (Nat.fib_pos.mpr hb).ne'
  rw [GoldenCubicBlockFibonacciLagProduct.cubic_block_fibonacci_lag_product n m hmn.le,
    padicValInt.mul (mul_ne_zero (by decide) hfa) hfb, padicValInt.mul (by decide) hfa,
    padicValInt.of_nat, padicValInt.of_nat, valuation_eq_readout p _ hp hp2 ha,
    valuation_eq_readout p _ hp hp2 hb]
  by_cases h : p=5
  · subst p
    have hval : padicValInt 5 (5:ℤ) = 1 := padicValInt_self
    simp only [hval, ite_true]
  · have hval : padicValInt p (5:ℤ) = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      intro hnat
      apply h
      have hdiv : p ∣ 5 := by exact_mod_cast hnat
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hdiv
    simp only [ite_eq_right h, hval]

/-- Convert the valuation to a collision test at every odd-prime power. -/
theorem cubic_block_odd_prime_rank_collision (p n m a : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hmn : m < n) :
    (goldenLucas (3^n)^2+3) ≡ (goldenLucas (3^m)^2+3) [ZMOD (p:ℤ)^a] ↔
      a ≤ (if p=5 then 1 else 0) + valuationReadout p (3^n+3^m) +
        valuationReadout p (3^n-3^m) := by
  let d : ℤ := (goldenLucas (3^n)^2+3)-(goldenLucas (3^m)^2+3)
  have hpow : (3:ℕ)^m < 3^n := Nat.pow_lt_pow_right (by decide) hmn
  have ha : 0 < (3:ℕ)^n+3^m := by positivity
  have hb : 0 < (3:ℕ)^n-3^m := Nat.sub_pos_of_lt hpow
  have hd : d ≠ 0 := by
    dsimp only [d]
    rw [GoldenCubicBlockFibonacciLagProduct.cubic_block_fibonacci_lag_product n m hmn.le]
    exact mul_ne_zero (mul_ne_zero (by decide) (by exact_mod_cast (Nat.fib_pos.mpr ha).ne'))
      (by exact_mod_cast (Nat.fib_pos.mpr hb).ne')
  rw [Int.modEq_iff_dvd, ← Int.dvd_neg,
    show -((goldenLucas (3^m)^2+3)-(goldenLucas (3^n)^2+3)) = d by dsimp [d]; ring,
    padicValInt_dvd_iff_of_ne_one hp.ne_one, or_iff_right hd]
  have hv : padicValInt p d = _ := cubic_block_odd_prime_rank_lag p n m hp hp2 hmn
  rw [hv]


/-- Every ordinary prime is covered, including the jump from level zero
to the positive-index dyadic orbit. -/
theorem cubic_block_all_prime_lag (p n m : ℕ) (hp : p.Prime) (hmn : m<n) :
    padicValInt p ((goldenLucas (3^n)^2+3)-(goldenLucas (3^m)^2+3)) =
      if p=2 then (if m=0 then 0 else 7+padicValNat 2 (n-m))
      else (if p=5 then 1 else 0) + valuationReadout p (3^n+3^m) +
        valuationReadout p (3^n-3^m) := by
  by_cases hp2 : p=2
  · subst p
    by_cases hm : m=0
    · subst m
      simp only [ite_true]
      have h0 : GoldenCubicDyadicClock.dyadicBlock 0 = 4 := by
        open D5.S0.Carrier in
        norm_num [GoldenCubicDyadicClock.dyadicBlock, goldenLucas, trace, phi]
      change padicValInt 2 (GoldenCubicDyadicClock.dyadicBlock n -
        GoldenCubicDyadicClock.dyadicBlock 0) = 0
      rw [h0]
      apply padicValInt.eq_zero_of_not_dvd
      intro h
      have hc := ((GoldenCubicDyadicClock.dyadicBlock_mod128 n (by omega)).of_dvd
        (by decide : (2:ℤ) ∣ 128)).sub (Int.ModEq.refl 4)
      have ht := (Int.modEq_zero_iff_dvd.mpr h).symm.trans hc
      exact (by decide : ¬ (0 ≡ 19-4 [ZMOD 2])) ht
    · simp only [ite_true, ite_eq_right hm]
      exact GoldenCubicDyadicClock.golden_cubic_dyadic_lag n m (by omega) hmn
  · simp only [ite_eq_right hp2]
    exact cubic_block_odd_prime_rank_lag p n m hp hp2 hmn


end D5.S3.Arith.Primes.GoldenCubicBlockRankReadout
