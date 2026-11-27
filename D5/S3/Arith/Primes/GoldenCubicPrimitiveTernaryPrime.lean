/- GID: D5/S3/Arith/Primes/GoldenCubicPrimitiveTernaryPrime
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicPrimitiveTernaryPrime
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Every positive ternary power is the exact order of nine modulo a prime outside 2, 3, and 5. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.Primes.GoldenCubicPrimitiveTernaryPrime

/-- The third cyclotomic polynomial of a power of nine supplies a prime
which sees precisely one more ternary digit of the exponent. -/
theorem exists_prime_orderOf_nine_succ (n : ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 5 ∧
      orderOf (9 : ZMod q) = 3 ^ (n+1) := by
  let m := (3 : ℕ)^n
  let F := ((9:ℕ)^m)^2 + (9:ℕ)^m + 1
  have hm : 0 < m := pow_pos (by decide) _
  have hF : F ≠ 1 := by
    have hp : 0 < (9:ℕ)^m := pow_pos (by decide) _
    dsimp [F]
    omega
  obtain ⟨q,hq,hqF⟩ := Nat.exists_prime_and_dvd hF
  have hz : ((9 : ZMod q)^m)^2 + (9 : ZMod q)^m + 1 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff F q).2 hqF
    simpa [F] using h
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hh (x : ZMod 2) : x^2+x+1 ≠ 0 := by fin_cases x <;> decide
    exact hh _ hz
  have hq3 : q ≠ 3 := by
    rintro rfl
    have hh : (9 : ZMod 3)^m = 0 := by
      rw [show (9 : ZMod 3) = 0 by decide, zero_pow hm.ne']
    rw [hh] at hz
    exact (by decide : ((0 : ZMod 3)^2+0+1) ≠ 0) hz
  have hq5 : q ≠ 5 := by
    rintro rfl
    have hh (x : ZMod 5) : x^2+x+1 ≠ 0 := by fin_cases x <;> decide
    exact hh _ hz
  refine ⟨q,hq,hq2,hq3,hq5,?_⟩
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime_pow (p := 3) (n := n)
  · intro h
    change (9 : ZMod q)^m = 1 at h
    rw [h] at hz
    have h3 : ((3 : ℕ) : ZMod q) = 0 := by convert hz using 1; ring
    exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1
      ((ZMod.natCast_eq_zero_iff 3 q).1 h3))
  · rw [show (3:ℕ)^(n+1) = m*3 by rw [pow_succ]]
    rw [pow_mul]
    have hpoly : ((9 : ZMod q)^m)^3 - 1 = 0 := by
      calc
        _ = ((9 : ZMod q)^m-1) * (((9 : ZMod q)^m)^2+(9 : ZMod q)^m+1) := by ring
        _ = 0 := by rw [hz,mul_zero]
    exact sub_eq_zero.mp hpoly

theorem exists_prime_orderOf_nine (k : ℕ) (hk : 0 < k) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 5 ∧
      orderOf (9 : ZMod q) = 3 ^ k := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  exact exists_prime_orderOf_nine_succ n

end D5.S3.Arith.Primes.GoldenCubicPrimitiveTernaryPrime
