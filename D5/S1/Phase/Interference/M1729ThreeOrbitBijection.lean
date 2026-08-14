/- GID: D5/S1/Phase/Interference/M1729ThreeOrbitBijection
   generality: I
   mirror-B: D5/B/S1/Phase/Interference/M1729ThreeOrbitBijection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factor 1729 and identify its three singleton prime-factor choices. -/

/- Library-search audit trail (2026-08-14):
   * No complete statement for 1729 was found in pinned Mathlib or D5.
   * `Nat.primeFactors_mul` and `Nat.Prime.primeFactors` compute the exact
     prime-factor set without introducing a second factorization interface.
   * `Fintype.equivFinOfCardEq` packages the cardinal certificate as a
     bijection, while the existing three-singleton theorem supplies the count.
-/

import D5.S1.Phase.SeatTowerConsequences
import Mathlib.Data.Nat.PrimeFin

namespace D5.S1.Phase.Interference.M1729ThreeOrbitBijection

open D5.S1.Phase.SeatTowerConsequences

/-- The factorization of 1729 has exactly three prime factors, and choosing
one of them is equivalent to choosing an element of `Fin 3`. -/
theorem m1729_three_orbit_bijection :
    (1729 : Nat) = 7 * 13 * 19 ∧
      (Nat.Prime 7 ∧ Nat.Prime 13 ∧ Nat.Prime 19) ∧
        (1729 : Nat).primeFactors = {7, 13, 19} ∧
          Nonempty (↥((1729 : Nat).primeFactors.powersetCard 1) ≃ Fin 3) := by
  have hFactor : (1729 : Nat) = 7 * 13 * 19 := by norm_num
  have hp7 : Nat.Prime 7 := by decide
  have hp13 : Nat.Prime 13 := by decide
  have hp19 : Nat.Prime 19 := by decide
  have hPrimeFactors : (1729 : Nat).primeFactors = {7, 13, 19} := by
    calc
      (1729 : Nat).primeFactors = (7 * 13 * 19).primeFactors := by rw [hFactor]
      _ = (7 * 13).primeFactors ∪ (19 : Nat).primeFactors := by
        rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
      _ = ((7 : Nat).primeFactors ∪ (13 : Nat).primeFactors) ∪
          (19 : Nat).primeFactors := by
        rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
      _ = {7, 13, 19} := by
        simp [hp7.primeFactors, hp13.primeFactors, hp19.primeFactors]
  refine ⟨hFactor, ⟨hp7, hp13, hp19⟩, hPrimeFactors, ?_⟩
  refine ⟨Fintype.equivFinOfCardEq ?_⟩
  rw [Fintype.card_coe]
  calc
    ((1729 : Nat).primeFactors.powersetCard 1).card =
        ((Finset.univ : Finset (Fin 3)).powersetCard 1).card := by
      rw [hPrimeFactors, Finset.card_powersetCard, Finset.card_powersetCard]
      norm_num
    _ = 3 := three_split_primes_have_three_singleton_choices

/-- The concrete number domain used by the statement is inhabited. -/
example : Nat := 1729

/-- The assumption-free theorem has an explicit checked proof term. -/
example :
    (1729 : Nat) = 7 * 13 * 19 ∧
      (Nat.Prime 7 ∧ Nat.Prime 13 ∧ Nat.Prime 19) ∧
        (1729 : Nat).primeFactors = {7, 13, 19} ∧
          Nonempty (↥((1729 : Nat).primeFactors.powersetCard 1) ≃ Fin 3) :=
  m1729_three_orbit_bijection

/- Omitting one of the certified prime factors changes the statement. -/
example : (1729 : Nat).primeFactors ≠ {7, 13} := by
  rw [m1729_three_orbit_bijection.2.2.1]
  decide

#print axioms m1729_three_orbit_bijection

end D5.S1.Phase.Interference.M1729ThreeOrbitBijection
