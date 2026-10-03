/- GID: D5/S3/Arith/GoldenFibonacciModulusPeriod
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenFibonacciModulusPeriod
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Odd Fibonacci moduli have exact fourfold matrix period. -/

import D5.S3.Arith.GoldenApparition
import Mathlib.Data.Matrix.Reflection
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.Fib.Lemmas

namespace D5.S3.Arith.GoldenFibonacciModulusPeriod

open scoped Matrix
open D5.S0.Carrier D5.S1.Scale
open D5.S3.Arith.GoldenApparition

def multiplicationMatrix (m : ℕ) (z : GoldenMod m) :
    Matrix (Fin 2) (Fin 2) (ZMod m) :=
  !![z.a + z.b, z.b; z.b, z.a]

def goldenMatrixHom (m : ℕ) :
    GoldenMod m →+* Matrix (Fin 2) (Fin 2) (ZMod m) where
  toFun := multiplicationMatrix m
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [multiplicationMatrix]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [multiplicationMatrix]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [multiplicationMatrix, add_left_comm, add_comm]
  map_mul' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [multiplicationMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem fib_index_dvd_of_fib_dvd {n t : ℕ} (hn : 5 ≤ n)
    (h : Nat.fib n ∣ Nat.fib t) : n ∣ t := by
  have hfib : 5 ≤ Nat.fib n := by
    calc
      5 = Nat.fib 5 := by decide
      _ ≤ Nat.fib n := Nat.fib_mono hn
  have hg : Nat.fib (Nat.gcd n t) = Nat.fib n := by
    rw [Nat.fib_gcd, Nat.gcd_eq_left_iff_dvd.mpr h]
  have hg2 : 2 ≤ Nat.gcd n t := by
    by_contra hsmall
    have hcases : Nat.gcd n t = 0 ∨ Nat.gcd n t = 1 := by omega
    rcases hcases with hzero | hone
    · rw [hzero] at hg
      simp at hg
      omega
    · rw [hone] at hg
      simp at hg
      omega
  have heq : Nat.gcd n t = n := by
    have hle := Nat.gcd_le_left t (by omega : 0 < n)
    by_contra hne
    have hlt : Nat.gcd n t < n := by omega
    have hFibLt := (Nat.fib_lt_fib hg2).2 hlt
    omega
  exact Nat.gcd_eq_left_iff_dvd.mp heq

/-- For odd indices at least five, the Fibonacci matrix modulo its own
Fibonacci value first returns after four times the index. -/
theorem golden_fibonacci_modulus_period (n : ℕ) (hn : 5 ≤ n) (hodd : Odd n) :
    orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (Nat.fib n))) =
      4 * n := by
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
  let m := Nat.fib n
  have hmge : 5 ≤ m := by
    dsimp [m]
    calc
      5 = Nat.fib 5 := by decide
      _ ≤ Nat.fib n := Nat.fib_mono hn
  have hreduce : GoldenMod.reduce m D5.S0.Carrier.phi = GoldenMod.phi := by
    ext <;> norm_num [GoldenMod.reduce, D5.S0.Carrier.phi, GoldenMod.phi]
  have hpair (k : ℕ) :
      (GoldenMod.phi : GoldenMod m) ^ (k + 1) =
        ⟨(Nat.fib k : ZMod m), (Nat.fib (k + 1) : ZMod m)⟩ := by
    have h := congrArg (GoldenMod.reduce m) (golden_phi_pow_eq_fib_pair k)
    simpa [map_pow, hreduce, GoldenMod.reduce, GoldenMod.phi] using h
  have hnidx : n - 1 + 1 = n := by omega
  have hpow : (GoldenMod.phi : GoldenMod m) ^ n =
      (Nat.fib (n - 1) : GoldenMod m) := by
    have h := hpair (n - 1)
    rw [hnidx] at h
    apply GoldenMod.ext
    · simpa using congrArg GoldenMod.a h
    · have hb := congrArg GoldenMod.b h
      simpa [m] using hb
  have hcass : ((Nat.fib (n - 1) : ZMod m) ^ 2) = -1 := by
    have h := fib_cassini_from_golden_norm (n - 2)
    have hidx1 : n - 2 + 1 = n - 1 := by omega
    have hidx2 : n - 2 + 2 = n := by omega
    have heven : Even (n - 1) := by
      rcases hodd with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      omega
    rw [hidx1, hidx2, heven.neg_one_pow] at h
    have hz := congrArg (fun z : ℤ => (z : ZMod m)) h
    have hzero : (Nat.fib n : ZMod m) = 0 := by
      exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_refl m)
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      Int.cast_one] at hz
    rw [hzero, mul_zero, zero_sub] at hz
    exact (neg_eq_iff_eq_neg).mp hz
  have hsquare : ((GoldenMod.phi : GoldenMod m) ^ n) ^ 2 = -1 := by
    rw [hpow]
    apply GoldenMod.ext
    · simpa [pow_two, GoldenMod.a_mul] using hcass
    · simp [pow_two, GoldenMod.b_mul]
  have hfour : ((GoldenMod.phi : GoldenMod m) ^ n) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hsquare]
    norm_num
  have htwozero : (2 : ZMod m) ≠ 0 := by
    intro hzero
    have hdvd : m ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp hzero
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hdvd
    omega
  have hneg : (-1 : GoldenMod m) ≠ 1 := by
    intro heq
    have ha := congrArg GoldenMod.a heq
    have hbad : (2 : ZMod m) = 0 := by
      have hne : (-1 : ZMod m) = 1 := by simpa using ha
      calc
        (2 : ZMod m) = 1 + 1 := by ring
        _ = -1 + 1 := by rw [hne]
        _ = 0 := by ring
    exact htwozero hbad
  let x : GoldenMod m := GoldenMod.phi
  have horderDvd : orderOf (x ^ n) ∣ 4 :=
    orderOf_dvd_of_pow_eq_one hfour
  have horderNotTwo : ¬ orderOf (x ^ n) ∣ 2 := by
    intro hdvd
    have hreturn : (x ^ n) ^ 2 = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd
    exact hneg (hsquare.symm.trans hreturn)
  have horderFour : orderOf (x ^ n) = 4 := by
    have hpos : 0 < orderOf (x ^ n) := by
      by_contra hnot
      have hzero : orderOf (x ^ n) = 0 := by omega
      rw [hzero] at horderDvd
      norm_num at horderDvd
    have hle : orderOf (x ^ n) ≤ 4 := Nat.le_of_dvd (by decide) horderDvd
    interval_cases orderOf (x ^ n) <;> norm_num at *
  have htDvd : orderOf x ∣ 4 * n := by
    apply orderOf_dvd_of_pow_eq_one
    rw [show 4 * n = n * 4 by omega, pow_mul]
    exact hfour
  have htpos : 0 < orderOf x := by
    by_contra hnot
    have hzero : orderOf x = 0 := by omega
    rw [hzero] at htDvd
    norm_num at htDvd
    omega
  have htFib : m ∣ Nat.fib (orderOf x) := by
    have hidx : orderOf x - 1 + 1 = orderOf x := by omega
    have h := hpair (orderOf x - 1)
    rw [hidx, pow_orderOf_eq_one] at h
    have hb := congrArg GoldenMod.b h
    have hzero : (Nat.fib (orderOf x) : ZMod m) = 0 := by
      simpa using hb.symm
    exact (ZMod.natCast_eq_zero_iff _ _).mp hzero
  have hndvd : n ∣ orderOf x := fib_index_dvd_of_fib_dvd hn htFib
  have hdiv : orderOf x / n = 4 := by
    rw [← horderFour]
    exact (orderOf_pow_of_dvd (by omega : n ≠ 0) hndvd).symm
  have hxorder : orderOf x = 4 * n := by
    have hmul := Nat.div_mul_cancel hndvd
    rw [hdiv] at hmul
    omega
  rw [← hMatrixOrder m]
  exact hxorder

#print axioms golden_fibonacci_modulus_period

end D5.S3.Arith.GoldenFibonacciModulusPeriod
