/- GID: D5/S3/ArithUnits/MercaPrimeCharacterMoment
   generality: G
   mirror-B: D5/B/S3/ArithUnits/MercaPrimeCharacterMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native unit representative moment of a prime odd character is nonzero. -/

import D5.S3.Analytic.Zeta.CatalanPrimeOddMoment
import D5.S3.ArithUnits.MercaCosetFiberLift

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace D5.S3.ArithUnits.MercaPrimeCharacterMoment

/-- The character moment on the same actual units and representatives as the Merca coset route. -/
def characterMoment (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) : ℂ :=
  ∑ u : (ZMod n)ˣ, ((u : ZMod n).val : ℂ) * χ (u : ZMod n)

/-- Nonunits contribute zero; the unit coercion enumerates every remaining summand once. -/
theorem character_moment_eq_zmod_sum (n : ℕ) [NeZero n]
    (χ : DirichletCharacter ℂ n) :
    characterMoment n χ = ∑ a : ZMod n, (a.val : ℂ) * χ a := by
  classical
  let e : (ZMod n)ˣ ↪ ZMod n := ⟨Units.val, Units.val_injective⟩
  calc
    characterMoment n χ =
        ∑ a ∈ Finset.univ.map e, (a.val : ℂ) * χ a := by
      simp [characterMoment, e]
    _ = ∑ a : ZMod n, (a.val : ℂ) * χ a := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ ha
      have hn : ¬ IsUnit a := by
        intro hu
        apply ha
        exact Finset.mem_map.mpr ⟨hu.unit, Finset.mem_univ _, hu.unit_spec⟩
      rw [χ.map_nonunit hn, mul_zero]

/-- This is the prime, nonprincipal, odd-character prerequisite of the collision converse. -/
theorem prime_odd_character_moment_ne_zero (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (hodd : χ.Odd) :
    characterMoment p χ ≠ 0 := by
  rw [character_moment_eq_zmod_sum]
  exact D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.odd_character_weighted_sum_ne_zero
    p χ hχ hodd

end D5.S3.ArithUnits.MercaPrimeCharacterMoment
