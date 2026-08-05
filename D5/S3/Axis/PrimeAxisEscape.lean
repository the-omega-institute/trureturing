/- GID: D5/S3/Axis/PrimeAxisEscape
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite prime axis is escaped by a prime divisor of the product plus one. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

namespace D5.S3.Axis.PrimeAxisEscape

/-- The product of a finite set of primes plus one is congruent to one modulo
each prime in the set and has a prime divisor outside the set. -/
theorem prime_axis_escape (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    (∀ p ∈ S, Nat.ModEq p (S.prod id + 1) 1) ∧
      ∃ q, Nat.Prime q ∧ q ∣ S.prod id + 1 ∧ q ∉ S := by
  constructor
  · intro p hp
    have hp_dvd_prod : p ∣ S.prod id := Finset.dvd_prod_of_mem id hp
    simpa using
      (Nat.modEq_zero_iff_dvd.mpr hp_dvd_prod).add (Nat.ModEq.refl 1)
  · have hprod_pos : 0 < S.prod id :=
      Finset.prod_pos fun p hp => (hS p hp).pos
    obtain ⟨q, hq_prime, hq_dvd⟩ :=
      Nat.exists_prime_and_dvd (n := S.prod id + 1) (by omega)
    refine ⟨q, hq_prime, hq_dvd, ?_⟩
    intro hq_mem
    have hq_dvd_prod : q ∣ S.prod id := Finset.dvd_prod_of_mem id hq_mem
    have hq_dvd_one : q ∣ 1 := (Nat.dvd_add_iff_right hq_dvd_prod).mpr hq_dvd
    exact hq_prime.not_dvd_one hq_dvd_one

end D5.S3.Axis.PrimeAxisEscape
