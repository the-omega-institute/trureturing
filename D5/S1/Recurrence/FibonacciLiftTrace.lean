/- GID: D5/S1/Recurrence/FibonacciLiftTrace
   generality: G
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:exact-first-lift-scalar-reduction)
   anchors: []
   digest: For every odd prime the actual first return defect has zero trace, so one Fibonacci quotient decides period retention at the prime square. -/

import D5.S1.Recurrence.FibonacciPrimeSquareLift
import Mathlib.Algebra.Ring.Parity

set_option autoImplicit false

namespace D5.S1.Recurrence.FibonacciLiftTrace

open Matrix FibonacciReturnSpectrum FibonacciPrimeSquareLift
open scoped Matrix

lemma fibUnit_det_power (R : Type*) [CommRing R] (t : ℕ) :
    (↑(fibUnit R ^ t) : Matrix (Fin 2) (Fin 2) R).det = (-1 : R) ^ t := by
  rw [Units.val_pow, Matrix.det_pow]
  congr 1
  simp [fibUnit, LucasEvenDescent.companion, Matrix.det_fin_two]

/-- The determinant forces every return at an odd prime to have even time. -/
theorem period_even (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : Even (period p) := by
  have hu : fibUnit (ZMod p) ^ period p = 1 := pow_orderOf_eq_one _
  have hd : (-1 : ZMod p) ^ period p = 1 := by
    rw [← fibUnit_det_power, hu]
    simp
  rcases Nat.even_or_odd (period p) with he | ho
  · exact he
  · rw [ho.neg_one_pow] at hd
    have hz : (2 : ZMod p) = 0 := by linear_combination -hd
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hdiv
    have hge := hp.two_le
    omega

/-- At an even return, Cassini reduces the integral first-lift trace by an additional p.
The identity is over integers, so no cancellation by p in ZMod(p^2) is performed. -/
theorem quotient_trace_identity (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    let a : ℤ := firstQuotient p (period p)
    let b : ℤ := secondQuotient p (period p)
    2 * b - a = -(p : ℤ) * (b ^ 2 - a * b - a ^ 2) := by
  dsimp only
  have hreturn : p ∣ returnContent (period p) :=
    (period_dvd_iff_dvd_returnContent p (period p)).mp (dvd_refl _)
  have hparts := Nat.dvd_gcd_iff.mp hreturn
  have ha : Nat.fib (period p) = p * firstQuotient p (period p) :=
    (Nat.mul_div_cancel' hparts.1).symm
  have hfpos : 1 ≤ Nat.fib (period p + 1) := Nat.fib_pos.mpr (by omega)
  have hb : Nat.fib (period p + 1) = 1 + p * secondQuotient p (period p) := by
    have he := Nat.mul_div_cancel' hparts.2
    change p * secondQuotient p (period p) = Nat.fib (period p + 1) - 1 at he
    omega
  have hd := fibUnit_det_power ℤ (period p)
  rw [fibUnit_power, (period_even p hp hp2).neg_one_pow] at hd
  simp only [Matrix.det_fin_two_of] at hd
  rw [ha, hb] at hd
  push_cast at hd
  have hprod : (p : ℤ) *
      (2 * (secondQuotient p (period p) : ℤ) - (firstQuotient p (period p) : ℤ) +
        (p : ℤ) * ((secondQuotient p (period p) : ℤ) ^ 2 -
          (firstQuotient p (period p) : ℤ) * (secondQuotient p (period p) : ℤ) -
          (firstQuotient p (period p) : ℤ) ^ 2)) = 0 := by
    linear_combination hd
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have he := (mul_eq_zero.mp hprod).resolve_left hpz
  linarith

/-- The normalized first-return matrix has zero trace modulo the odd prime. -/
theorem quotient_trace_zero (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (2 : ZMod p) * (secondQuotient p (period p) : ZMod p) =
      (firstQuotient p (period p) : ZMod p) := by
  have h := congrArg (fun z : ℤ => (z : ZMod p)) (quotient_trace_identity p hp hp2)
  push_cast at h
  simpa only [ZMod.natCast_self, neg_zero, zero_mul, sub_eq_zero] using h

/-- Only one quotient residue is required at odd primes. This includes the ramified prime 5. -/
theorem square_period_eq_iff_firstQuotient (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    period (p ^ 2) = period p ↔ p ∣ firstQuotient p (period p) := by
  rw [square_period_eq_iff_quotients p hp.pos]
  constructor
  · exact And.left
  · intro ha
    refine ⟨ha, ?_⟩
    letI : Fact p.Prime := ⟨hp⟩
    have haz : (firstQuotient p (period p) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ p).mpr ha
    have htrace := quotient_trace_zero p hp hp2
    rw [haz] at htrace
    have htwo : (2 : ZMod p) ≠ 0 := by
      intro hz
      have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp hz
      have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
      have hge := hp.two_le
      omega
    exact (ZMod.natCast_eq_zero_iff _ p).mp
      ((mul_eq_zero.mp htrace).resolve_left htwo)

/-- A nonzero scalar quotient certifies the complete p-fold period lift. -/
theorem full_lift_of_firstQuotient_nonzero (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (h : (firstQuotient p (period p) : ZMod p) ≠ 0) :
    period (p ^ 2) = p * period p := by
  rcases prime_square_period_dichotomy p hp with he | he
  · have ha := (square_period_eq_iff_firstQuotient p hp hp2).mp he
    exact (h ((ZMod.natCast_eq_zero_iff _ p).mpr ha)).elim
  · exact he

end D5.S1.Recurrence.FibonacciLiftTrace
