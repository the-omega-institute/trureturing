/- GID: D5/S3/Arith/Primes/GoldenCubicBlockPrimePeriods
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicBlockPrimePeriods
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Prime factors of golden cubic blocks have their exact Fibonacci matrix periods. -/

import D5.S3.Arith.Primes.GoldenCubicBlockRanks
import D5.S3.Arith.GoldenFibonacciModulusPeriod

namespace D5.S3.Arith.Primes.GoldenCubicBlockPrimePeriods

open scoped Matrix
open D5.S0.Carrier D5.S1.Scale
open D5.S3.Arith.GoldenApparition D5.S3.Arith.GoldenFibonacciModulusPeriod
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.Primes.GoldenCubicBlockRanks

/-- A prime dividing the Lucas cubic block has exactly the doubled ternary
Fibonacci matrix period. -/
theorem cubic_block_b_prime_period (j p : ℕ) (hj : 1 ≤ j) (hp : p.Prime)
    (hpB : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3) :
    orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      2 * 3 ^ (j + 1) := by
  have hMatrixOrder (m : ℕ) :
      orderOf (GoldenMod.phi : GoldenMod m) =
        orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m)) := by
    have hinj : Function.Injective (goldenMatrixHom m) := by
      intro x y h
      apply GoldenMod.ext
      · have h11 := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) (ZMod m) => M 1 1) h
        simpa [goldenMatrixHom, multiplicationMatrix] using h11
      · have h01 := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) (ZMod m) => M 0 1) h
        simpa [goldenMatrixHom, multiplicationMatrix] using h01
    have hphi : goldenMatrixHom m (GoldenMod.phi : GoldenMod m) =
        !![1, 1; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [goldenMatrixHom, multiplicationMatrix, GoldenMod.phi]
    have horder := orderOf_injective (goldenMatrixHom m).toMonoidHom
      hinj (GoldenMod.phi : GoldenMod m)
    change orderOf (goldenMatrixHom m (GoldenMod.phi : GoldenMod m)) = _ at horder
    rw [hphi] at horder
    exact horder.symm
  let n := 3 ^ (j + 1)
  have hnodd : Odd n := (by decide : Odd (3 : ℕ)).pow
  have hrank : fibonacciRank p = 2 * n := by
    simpa only [n] using (cubic_block_b_prime_rank j p hj hp hpB).1
  let r := rankWitness p hp
  have hrpos : 0 < r.val := r.property.1
  have hrzero : p ∣ Nat.fib r.val := r.property.2.1
  have hrmin : ∀ t, 0 < t → p ∣ Nat.fib t → r.val ≤ t := r.property.2.2
  have hrn : r.val = 2 * n := by
    simpa only [fibonacciRank, hp, dite_true] using hrank
  have hpLucas : (p : ℤ) ∣ goldenLucas n := by
    change (p : ℤ) ∣ goldenLucas (3 ^ (j + 1))
    rw [(golden_cubic_lucas_block j hj).2.2.2.2.2]
    exact dvd_mul_of_dvd_right hpB _
  have htrace : (trace (phi ^ n) : ZMod p) = 0 := by
    rw [← golden_lucas_eq_trace_phi_pow]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpLucas
  have htraceMod : ((trace (phi ^ n) : ℤ) : GoldenMod p) = 0 := by
    apply GoldenMod.ext
    · simpa using htrace
    · simp
  have hnorm : norm (phi ^ n) = -1 := by
    rw [norm_phi_pow, hnodd.neg_one_pow]
  have hreduce : GoldenMod.reduce p phi = GoldenMod.phi := by
    ext <;> norm_num [GoldenMod.reduce, phi, GoldenMod.phi]
  have hquad (z : GoldenInt) :
      z ^ 2 = (trace z : GoldenInt) * z - (norm z : GoldenInt) := by
    apply GoldenInt.ext <;>
      simp only [pow_two, sub_eq_add_neg, a_add, a_neg, a_mul,
        b_add, b_neg, b_mul, a_intCast, b_intCast,
        D5.S0.Carrier.trace, D5.S0.Carrier.norm] <;> ring
  have hsq : ((GoldenMod.phi : GoldenMod p) ^ n) ^ 2 = 1 := by
    have h := congrArg (GoldenMod.reduce p) (hquad (phi ^ n))
    simp only [map_pow, map_mul, map_sub, map_intCast, hreduce, hnorm,
      htraceMod, zero_mul, zero_sub, Int.cast_neg, Int.cast_one] at h
    simpa using h
  have hreturn : (GoldenMod.phi : GoldenMod p) ^ (2 * n) = 1 := by
    rw [Nat.mul_comm 2 n, pow_mul]
    exact hsq
  let x : GoldenMod p := GoldenMod.phi
  have htDvd : orderOf x ∣ 2 * n := orderOf_dvd_of_pow_eq_one hreturn
  have htpos : 0 < orderOf x := by
    by_contra hnot
    have hz : orderOf x = 0 := by omega
    rw [hz] at htDvd
    norm_num at htDvd
    omega
  have hpair (t : ℕ) :
      (GoldenMod.phi : GoldenMod p) ^ (t + 1) =
        ⟨(Nat.fib t : ZMod p), (Nat.fib (t + 1) : ZMod p)⟩ := by
    have h := congrArg (GoldenMod.reduce p) (golden_phi_pow_eq_fib_pair t)
    simpa [map_pow, hreduce, GoldenMod.reduce, GoldenMod.phi] using h
  have htFib : p ∣ Nat.fib (orderOf x) := by
    have hidx : orderOf x - 1 + 1 = orderOf x := by omega
    have h := hpair (orderOf x - 1)
    rw [hidx, pow_orderOf_eq_one] at h
    have hb := congrArg GoldenMod.b h
    have hz : (Nat.fib (orderOf x) : ZMod p) = 0 := by simpa using hb.symm
    exact (ZMod.natCast_eq_zero_iff _ _).mp hz
  have hndvd : 2 * n ∣ orderOf x := by
    rw [← hrn]
    exact (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
      hrpos hrzero hrmin).mp htFib
  rw [← hMatrixOrder p]
  exact Nat.dvd_antisymm htDvd hndvd

#print axioms cubic_block_b_prime_period

/-- A prime dividing the Fibonacci cubic block has exactly the fourfold
ternary Fibonacci matrix period. -/
theorem cubic_block_c_prime_period (j p : ℕ) (hj : 1 ≤ j) (hp : p.Prime)
    (hpC : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 1) :
    orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      4 * 3 ^ (j + 1) := by
  have hMatrixOrder (m : ℕ) :
      orderOf (GoldenMod.phi : GoldenMod m) =
        orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m)) := by
    have hinj : Function.Injective (goldenMatrixHom m) := by
      intro x y h
      apply GoldenMod.ext
      · have h11 := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) (ZMod m) => M 1 1) h
        simpa [goldenMatrixHom, multiplicationMatrix] using h11
      · have h01 := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) (ZMod m) => M 0 1) h
        simpa [goldenMatrixHom, multiplicationMatrix] using h01
    have hphi : goldenMatrixHom m (GoldenMod.phi : GoldenMod m) =
        !![1, 1; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [goldenMatrixHom, multiplicationMatrix, GoldenMod.phi]
    have horder := orderOf_injective (goldenMatrixHom m).toMonoidHom
      hinj (GoldenMod.phi : GoldenMod m)
    change orderOf (goldenMatrixHom m (GoldenMod.phi : GoldenMod m)) = _ at horder
    rw [hphi] at horder
    exact horder.symm
  let n := 3 ^ (j + 1)
  have hnge : 5 ≤ n := by
    dsimp [n]
    calc
      5 ≤ 3 ^ (2 : ℕ) := by decide
      _ ≤ 3 ^ (j + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hnodd : Odd n := (by decide : Odd (3 : ℕ)).pow
  have hrank : fibonacciRank p = n := by
    simpa only [n] using (cubic_block_c_prime_rank j p hj hp hpC).1
  let r := rankWitness p hp
  have hrpos : 0 < r.val := r.property.1
  have hrzero : p ∣ Nat.fib r.val := r.property.2.1
  have hrmin : ∀ t, 0 < t → p ∣ Nat.fib t → r.val ≤ t := r.property.2.2
  have hrn : r.val = n := by
    simpa only [fibonacciRank, hp, dite_true] using hrank
  have hpFib : p ∣ Nat.fib n := by rw [← hrn]; exact hrzero
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    have hx72 := (golden_cubic_lucas_block j hj).1
    have hx2 : (goldenLucas (3 ^ j) : ZMod 2) = 0 := by
      have h := congrArg (ZMod.castHom (by decide : 2 ∣ 72) (ZMod 2)) hx72
      simpa only [map_intCast, map_ofNat, show (4 : ZMod 2) = 0 by decide] using h
    have hC0 : ((goldenLucas (3 ^ j) ^ 2 + 1 : ℤ) : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpC
    push_cast at hC0
    rw [hx2] at hC0
    exact (by decide : (1 : ZMod 2) ≠ 0) (by simpa using hC0)
  have hreduce : GoldenMod.reduce p phi = GoldenMod.phi := by
    ext <;> norm_num [GoldenMod.reduce, phi, GoldenMod.phi]
  have hpair (t : ℕ) :
      (GoldenMod.phi : GoldenMod p) ^ (t + 1) =
        ⟨(Nat.fib t : ZMod p), (Nat.fib (t + 1) : ZMod p)⟩ := by
    have h := congrArg (GoldenMod.reduce p) (golden_phi_pow_eq_fib_pair t)
    simpa [map_pow, hreduce, GoldenMod.reduce, GoldenMod.phi] using h
  have hnidx : n - 1 + 1 = n := by omega
  have hzero : (Nat.fib n : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hpFib
  have hpow : (GoldenMod.phi : GoldenMod p) ^ n =
      (Nat.fib (n - 1) : GoldenMod p) := by
    have h := hpair (n - 1)
    rw [hnidx] at h
    apply GoldenMod.ext
    · simpa using congrArg GoldenMod.a h
    · have hb := congrArg GoldenMod.b h
      simpa [hzero] using hb
  have hcass : ((Nat.fib (n - 1) : ZMod p) ^ 2) = -1 := by
    have h := fib_cassini_from_golden_norm (n - 2)
    have hidx1 : n - 2 + 1 = n - 1 := by omega
    have hidx2 : n - 2 + 2 = n := by omega
    have heven : Even (n - 1) := by
      rcases hnodd with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      omega
    rw [hidx1, hidx2, heven.neg_one_pow] at h
    have hz := congrArg (fun z : ℤ => (z : ZMod p)) h
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      Int.cast_one] at hz
    rw [hzero, mul_zero, zero_sub] at hz
    exact (neg_eq_iff_eq_neg).mp hz
  have hsquare : ((GoldenMod.phi : GoldenMod p) ^ n) ^ 2 = -1 := by
    rw [hpow]
    apply GoldenMod.ext
    · simpa [pow_two, GoldenMod.a_mul] using hcass
    · simp [pow_two, GoldenMod.b_mul]
  have hfour : ((GoldenMod.phi : GoldenMod p) ^ n) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hsquare]
    norm_num
  have htwozero : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp hz
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp hdvd)
  have hneg : (-1 : GoldenMod p) ≠ 1 := by
    intro heq
    have ha := congrArg GoldenMod.a heq
    have hbad : (2 : ZMod p) = 0 := by
      have hne : (-1 : ZMod p) = 1 := by simpa using ha
      calc
        (2 : ZMod p) = 1 + 1 := by ring
        _ = -1 + 1 := by rw [hne]
        _ = 0 := by ring
    exact htwozero hbad
  let x : GoldenMod p := GoldenMod.phi
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
  have htFib : p ∣ Nat.fib (orderOf x) := by
    have hidx : orderOf x - 1 + 1 = orderOf x := by omega
    have h := hpair (orderOf x - 1)
    rw [hidx, pow_orderOf_eq_one] at h
    have hb := congrArg GoldenMod.b h
    have hz : (Nat.fib (orderOf x) : ZMod p) = 0 := by simpa using hb.symm
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
  rw [← hMatrixOrder p]
  exact hxorder

#print axioms cubic_block_c_prime_period

end D5.S3.Arith.Primes.GoldenCubicBlockPrimePeriods
