/- GID: D5/S1/Recurrence/FibonacciPrimeSquareLift
   generality: G
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:exact-prime-square-lift)
   anchors: []
   digest: A square-zero first return defect proves the actual prime-square period dichotomy and its exact quotient test. -/

import D5.S1.Recurrence.FibonacciReturnSpectrum

set_option autoImplicit false

namespace D5.S1.Recurrence.FibonacciPrimeSquareLift

open Matrix FibonacciReturnSpectrum
open scoped Matrix

private theorem one_add_pow_of_square_zero {R : Type*} [Ring R]
    (x : R) (hx : x * x = 0) (n : ℕ) : (1 + x) ^ n = 1 + n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih]
      simp only [add_mul, one_mul, mul_add, mul_one, nsmul_mul,
        hx, nsmul_zero, add_zero, add_nsmul, one_nsmul]
      abel

/-- Any return modulo p lifts to a return at p times that time modulo p squared.
Primality is unnecessary for this implication. -/
theorem return_lifts_to_square (p t : ℕ) (h : p ∣ returnContent t) :
    period (p ^ 2) ∣ t * p := by
  have hfpos : 1 ≤ Nat.fib (t + 1) := Nat.fib_pos.mpr (by omega)
  rcases (Nat.dvd_gcd_iff.mp h) with ⟨h0, h1⟩
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  have hb' : Nat.fib (t + 1) = 1 + p * b := by omega
  let R := ZMod (p ^ 2)
  let B : Matrix (Fin 2) (Fin 2) R := !![(b : R), (a : R); (a : R), (b : R) - a]
  let D : Matrix (Fin 2) (Fin 2) R := (p : R) • B
  have hp2 : (p : R) ^ 2 = 0 := by
    change (p : ZMod (p ^ 2)) ^ 2 = 0
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hD : D * D = 0 := by
    have he : D * D = (p : R) ^ 2 • (B * B) := by
      ext i j
      simp only [D, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]
      ring
    rw [he, hp2, zero_smul]
  have hnD : p • D = 0 := by
    ext i j
    change (p • ((p : R) * B i j) : R) = 0
    rw [nsmul_eq_mul, ← mul_assoc, ← pow_two, hp2, zero_mul]
  have hshape : (↑(fibUnit R ^ t) : Matrix (Fin 2) (Fin 2) R) = 1 + D := by
    rw [fibUnit_power]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, B, ha, hb', Nat.cast_add, Nat.cast_mul] <;> ring
  have hpow : fibUnit R ^ (t * p) = 1 := by
    apply Units.ext
    rw [pow_mul, Units.val_pow, hshape,
      one_add_pow_of_square_zero D hD, hnD, add_zero]
  exact orderOf_dvd_iff_pow_eq_one.mpr hpow

/-- The actual period modulo p squared is either unchanged or multiplied by p.
This includes p=2 and p=5, rather than silently discarding small or ramified primes. -/
theorem prime_square_period_dichotomy (p : ℕ) (hp : p.Prime) :
    period (p ^ 2) = period p ∨ period (p ^ 2) = p * period p := by
  have hr : 0 < period p := period_pos p hp.pos
  have hbase : period p ∣ period (p ^ 2) :=
    period_dvd_of_dvd ⟨p, by simp [pow_two]⟩
  have hbound : period (p ^ 2) ∣ period p * p :=
    return_lifts_to_square p (period p)
      ((period_dvd_iff_dvd_returnContent p (period p)).mp (dvd_refl _))
  obtain ⟨k, hk⟩ := hbase
  obtain ⟨s, hs⟩ := hbound
  have hkp : k ∣ p := by
    refine ⟨s, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left hr
    simpa only [hk, Nat.mul_assoc] using hs
  rcases (Nat.dvd_prime hp).mp hkp with h | h
  · left
    simpa only [h, Nat.mul_one] using hk
  · right
    simpa only [h, Nat.mul_comm] using hk

/-- The nonexceptional branch has the full p-fold period, not merely an upper bound. -/
theorem prime_square_period_of_nonreturn (p : ℕ) (hp : p.Prime)
    (h : ¬ p ^ 2 ∣ returnContent (period p)) : period (p ^ 2) = p * period p := by
  rcases prime_square_period_dichotomy p hp with he | he
  · exact (h ((square_period_eq_iff p).mp he)).elim
  · exact he

/-- First lift data are obtained by exact integer division of the two return defects. -/
def firstQuotient (p t : ℕ) : ℕ := Nat.fib t / p
def secondQuotient (p t : ℕ) : ℕ := (Nat.fib (t + 1) - 1) / p

private theorem square_dvd_iff_quotient (p a : ℕ) (hp : 0 < p) (hpa : p ∣ a) :
    p ^ 2 ∣ a ↔ p ∣ a / p := by
  have ha : a = p * (a / p) := (Nat.mul_div_cancel' hpa).symm
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left hp
    calc
      p * (a / p) = a := ha.symm
      _ = p ^ 2 * k := hk
      _ = p * (p * k) := by ring
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [ha, hk]
    ring

/-- Both entries of the exact first lift vanish precisely when the p-period survives at p squared. -/
theorem square_period_eq_iff_quotients (p : ℕ) (hp : 0 < p) :
    period (p ^ 2) = period p ↔
      p ∣ firstQuotient p (period p) ∧ p ∣ secondQuotient p (period p) := by
  have hreturn : p ∣ returnContent (period p) :=
    (period_dvd_iff_dvd_returnContent p (period p)).mp (dvd_refl _)
  have hparts := Nat.dvd_gcd_iff.mp hreturn
  rw [square_period_eq_iff, returnContent, Nat.dvd_gcd_iff,
    square_dvd_iff_quotient p _ hp hparts.1,
    square_dvd_iff_quotient p _ hp hparts.2]
  rfl

/-- At the old period, the matrix defect is explicitly I+pB, in the original Fibonacci basis. -/
theorem first_lift_matrix (p : ℕ) (hp : 0 < p) :
    let r := period p
    let a : ZMod (p ^ 2) := firstQuotient p r
    let b : ZMod (p ^ 2) := secondQuotient p r
    (↑(fibUnit (ZMod (p ^ 2)) ^ r) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ 2))) =
      1 + (p : ZMod (p ^ 2)) • !![b, a; a, b - a] := by
  dsimp only
  have hreturn : p ∣ returnContent (period p) :=
    (period_dvd_iff_dvd_returnContent p (period p)).mp (dvd_refl _)
  have hparts := Nat.dvd_gcd_iff.mp hreturn
  have ha : Nat.fib (period p) = p * firstQuotient p (period p) := by
    exact (Nat.mul_div_cancel' hparts.1).symm
  have hfpos : 1 ≤ Nat.fib (period p + 1) := Nat.fib_pos.mpr (by omega)
  have hb : Nat.fib (period p + 1) = 1 + p * secondQuotient p (period p) := by
    have he := Nat.mul_div_cancel' hparts.2
    change p * secondQuotient p (period p) = Nat.fib (period p + 1) - 1 at he
    omega
  rw [fibUnit_power]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ha, hb, Nat.cast_add, Nat.cast_mul] <;> ring

end D5.S1.Recurrence.FibonacciPrimeSquareLift
