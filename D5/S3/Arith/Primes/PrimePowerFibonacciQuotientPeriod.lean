/- GID: D5/S3/Arith/Primes/PrimePowerFibonacciQuotientPeriod
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/PrimePowerFibonacciQuotientPeriod
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Prime factors of prime-power Fibonacci quotients have exact fourfold periods. -/

import D5.S3.Arith.Primes.PrimePowerFibonacciQuotientRank
import D5.S3.Arith.GoldenMatrixPeriodBridge

namespace D5.S3.Arith.Primes.PrimePowerFibonacciQuotientPeriod

open scoped Matrix
open D5.S0.Carrier D5.S1.Scale
open D5.S3.Arith.GoldenApparition D5.S3.Arith.GoldenMatrixPeriodBridge
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.Primes.PrimePowerFibonacciQuotientRank

/-- A prime first appearing in a consecutive prime-power Fibonacci quotient
has the full fourfold Fibonacci matrix period. -/
theorem prime_power_fibonacci_quotient_period (p k q : ℕ) (hp : p.Prime)
    (hpFive : 5 < p) (hq : q.Prime)
    (hqR : q ∣ Nat.fib (p ^ (k + 1)) / Nat.fib (p ^ k)) :
    orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      4 * p ^ (k + 1) := by
  let n := p ^ (k + 1)
  have hnge : 5 ≤ n := by
    have hpow : 0 < p ^ k := pow_pos hp.pos k
    dsimp [n]
    rw [pow_succ]
    nlinarith
  have hnodd : Odd n := by
    exact (hp.odd_of_ne_two (by omega)).pow
  have hqRank : fibonacciRank q = n := by
    simpa only [n] using
      (prime_power_fibonacci_quotient_rank p k hp hpFive).2 q hq hqR
  let r := rankWitness q hq
  have hrpos : 0 < r.val := r.property.1
  have hrzero : q ∣ Nat.fib r.val := r.property.2.1
  have hrmin : ∀ t, 0 < t → q ∣ Nat.fib t → r.val ≤ t := r.property.2.2
  have hrn : r.val = n := by
    simpa only [fibonacciRank, hq, dite_true, n] using hqRank
  have hqFib : q ∣ Nat.fib n := by rw [← hrn]; exact hrzero
  have hqgt : 2 < q := by
    have hqne : q ≠ 2 := by
      intro heq
      subst q
      have hle : r.val ≤ 3 := hrmin 3 (by decide) (by decide)
      omega
    have htwo := hq.two_le
    omega
  have hreduce : GoldenMod.reduce q D5.S0.Carrier.phi = GoldenMod.phi := by
    ext <;> norm_num [GoldenMod.reduce, D5.S0.Carrier.phi, GoldenMod.phi]
  have hpair (t : ℕ) :
      (GoldenMod.phi : GoldenMod q) ^ (t + 1) =
        ⟨(Nat.fib t : ZMod q), (Nat.fib (t + 1) : ZMod q)⟩ := by
    have h := congrArg (GoldenMod.reduce q) (golden_phi_pow_eq_fib_pair t)
    simpa [map_pow, hreduce, GoldenMod.reduce, GoldenMod.phi] using h
  have hnidx : n - 1 + 1 = n := by omega
  have hzero : (Nat.fib n : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hqFib
  have hpow : (GoldenMod.phi : GoldenMod q) ^ n =
      (Nat.fib (n - 1) : GoldenMod q) := by
    have h := hpair (n - 1)
    rw [hnidx] at h
    apply GoldenMod.ext
    · simpa using congrArg GoldenMod.a h
    · have hb := congrArg GoldenMod.b h
      simpa [hzero] using hb
  have hcass : ((Nat.fib (n - 1) : ZMod q) ^ 2) = -1 := by
    have h := fib_cassini_from_golden_norm (n - 2)
    have hidx1 : n - 2 + 1 = n - 1 := by omega
    have hidx2 : n - 2 + 2 = n := by omega
    have heven : Even (n - 1) := by
      rcases hnodd with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      omega
    rw [hidx1, hidx2, heven.neg_one_pow] at h
    have hz := congrArg (fun z : ℤ => (z : ZMod q)) h
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      Int.cast_one] at hz
    rw [hzero, mul_zero, zero_sub] at hz
    exact (neg_eq_iff_eq_neg).mp hz
  have hsquare : ((GoldenMod.phi : GoldenMod q) ^ n) ^ 2 = -1 := by
    rw [hpow]
    apply GoldenMod.ext
    · simpa [pow_two, GoldenMod.a_mul] using hcass
    · simp [pow_two, GoldenMod.b_mul]
  have hfour : ((GoldenMod.phi : GoldenMod q) ^ n) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hsquare]
    norm_num
  have htwozero : (2 : ZMod q) ≠ 0 := by
    intro hz
    have hdvd : q ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hdvd
    omega
  have hneg : (-1 : GoldenMod q) ≠ 1 := by
    intro heq
    have ha := congrArg GoldenMod.a heq
    have hbad : (2 : ZMod q) = 0 := by
      have hne : (-1 : ZMod q) = 1 := by simpa using ha
      calc
        (2 : ZMod q) = 1 + 1 := by ring
        _ = -1 + 1 := by rw [hne]
        _ = 0 := by ring
    exact htwozero hbad
  let x : GoldenMod q := GoldenMod.phi
  have horderDvd : orderOf (x ^ n) ∣ 4 := orderOf_dvd_of_pow_eq_one hfour
  have horderNotTwo : ¬ orderOf (x ^ n) ∣ 2 := by
    intro hdvd
    have hreturn : (x ^ n) ^ 2 = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd
    exact hneg (hsquare.symm.trans hreturn)
  have horderFour : orderOf (x ^ n) = 4 := by
    have hpos : 0 < orderOf (x ^ n) := by
      by_contra hnot
      have hz : orderOf (x ^ n) = 0 := by omega
      rw [hz] at horderDvd
      norm_num at horderDvd
    have hle : orderOf (x ^ n) ≤ 4 := Nat.le_of_dvd (by decide) horderDvd
    interval_cases orderOf (x ^ n) <;> norm_num at *
  have htDvd : orderOf x ∣ 4 * n := by
    apply orderOf_dvd_of_pow_eq_one
    rw [show 4 * n = n * 4 by omega, pow_mul]
    exact hfour
  have htpos : 0 < orderOf x := by
    by_contra hnot
    have hz : orderOf x = 0 := by omega
    rw [hz] at htDvd
    norm_num at htDvd
    omega
  have htFib : q ∣ Nat.fib (orderOf x) := by
    have hidx : orderOf x - 1 + 1 = orderOf x := by omega
    have h := hpair (orderOf x - 1)
    rw [hidx, pow_orderOf_eq_one] at h
    have hb := congrArg GoldenMod.b h
    have hz : (Nat.fib (orderOf x) : ZMod q) = 0 := by simpa using hb.symm
    exact (ZMod.natCast_eq_zero_iff _ _).mp hz
  have hndvd : n ∣ orderOf x := by
    rw [← hrn]
    exact (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
      hrpos hrzero hrmin).mp htFib
  have hdiv : orderOf x / n = 4 := by
    rw [← horderFour]
    exact (orderOf_pow_of_dvd (by omega : n ≠ 0) hndvd).symm
  have hxorder : orderOf x = 4 * n := by
    have hmul := Nat.div_mul_cancel hndvd
    rw [hdiv] at hmul
    omega
  rw [← (golden_matrix_faithful q).2.2]
  exact hxorder

#print axioms prime_power_fibonacci_quotient_period

end D5.S3.Arith.Primes.PrimePowerFibonacciQuotientPeriod
