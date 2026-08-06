/- GID: D5/S3/PrimeForms/GoldenPrimeClassification
   generality: I
   mirror-B: D5/B/S3/PrimeForms/GoldenPrimeClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden primes split, remain inert, or ramify according to residue classes modulo five. -/

import D5.S3.Arith.GoldenSplitSufficient
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace D5.S3.PrimeForms.GoldenPrimeClassification

open D5.S0.Carrier
open D5.S3.Arith.GoldenPrimeSplitting
open D5.S3.Arith.GoldenSplitSufficient

private theorem zmod_five_nonzero_square_eq_one_or_four
    (z : ZMod 5) (hz : z ≠ 0) (hsquare : IsSquare z) : z = 1 ∨ z = 4 := by
  revert z
  decide

/-- For an odd prime other than five, five is a square modulo that prime exactly
when the prime is congruent to one or minus one modulo five. -/
theorem five_is_square_mod_prime_iff_mod_five_eq_one_or_four
    {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) (h2 : p ≠ 2) :
    IsSquare (5 : ZMod p) ↔ p % 5 = 1 ∨ p % 5 = 4 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hp5ne : (p : ZMod 5) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hdiv
    exact h5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp hdiv).symm
  have hfiveNe : (5 : ZMod p) ≠ 0 := by
    change ((5 : ℕ) : ZMod p) ≠ 0
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hdiv
    exact h5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hdiv)
  have hreciprocity : legendreSym p 5 = legendreSym 5 p :=
    legendreSym.quadratic_reciprocity_one_mod_four
      (p := 5) (q := p) (by norm_num) h2
  constructor
  · intro hfiveSquare
    have hlegendreFive : legendreSym p 5 = 1 :=
      (legendreSym.eq_one_iff' p hfiveNe).2 hfiveSquare
    have hlegendreP : legendreSym 5 p = 1 := by
      rw [← hreciprocity]
      exact hlegendreFive
    have hpSquare : IsSquare (p : ZMod 5) :=
      (legendreSym.eq_one_iff' 5 hp5ne).1 hlegendreP
    rcases zmod_five_nonzero_square_eq_one_or_four (p : ZMod 5) hp5ne hpSquare with
      hone | hfour
    · left
      have hval := congrArg ZMod.val hone
      norm_num [ZMod.val_natCast] at hval ⊢
      exact hval
    · right
      have hval := congrArg ZMod.val hfour
      norm_num [ZMod.val_natCast] at hval ⊢
      exact hval
  · intro hmod
    have hpSquare : IsSquare (p : ZMod 5) := by
      rcases hmod with hmod | hmod
      · refine ⟨1, ?_⟩
        rw [← ZMod.natCast_mod p 5, hmod]
        norm_num
      · refine ⟨2, ?_⟩
        rw [← ZMod.natCast_mod p 5, hmod]
        norm_num
    have hlegendreP : legendreSym 5 p = 1 :=
      (legendreSym.eq_one_iff' 5 hp5ne).2 hpSquare
    have hlegendreFive : legendreSym p 5 = 1 := by
      rw [hreciprocity]
      exact hlegendreP
    exact (legendreSym.eq_one_iff' p hfiveNe).1 hlegendreFive

/-- A prime other than five splits in the golden integers exactly in the two
square residue classes modulo five. -/
theorem golden_not_prime_iff_mod_five_eq_one_or_four {p : ℕ} (hp : p.Prime)
    (h5 : p ≠ 5) :
    ¬ Prime (p : GoldenInt) ↔ p % 5 = 1 ∨ p % 5 = 4 := by
  constructor
  · intro hnotPrime
    have hlt : p % 5 < 5 := Nat.mod_lt p (by norm_num)
    have hclasses :
        p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
      omega
    rcases hclasses with hzero | hone | htwo | hthree | hfour
    · exact (h5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp
        (Nat.dvd_of_mod_eq_zero hzero)).symm).elim
    · exact Or.inl hone
    · exact (hnotPrime (golden_prime_of_mod_five_eq_two_or_three hp (Or.inl htwo))).elim
    · exact (hnotPrime (golden_prime_of_mod_five_eq_two_or_three hp (Or.inr hthree))).elim
    · exact Or.inr hfour
  · exact golden_not_prime_of_mod_five_eq_one_or_four hp h5

/-- A prime other than five is inert in the golden integers exactly in the two
nonsquare residue classes modulo five. -/
theorem golden_prime_iff_mod_five_eq_two_or_three {p : ℕ} (hp : p.Prime)
    (h5 : p ≠ 5) :
    Prime (p : GoldenInt) ↔ p % 5 = 2 ∨ p % 5 = 3 := by
  constructor
  · intro hprime
    have hlt : p % 5 < 5 := Nat.mod_lt p (by norm_num)
    have hclasses :
        p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
      omega
    rcases hclasses with hzero | hone | htwo | hthree | hfour
    · exact (h5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp
        (Nat.dvd_of_mod_eq_zero hzero)).symm).elim
    · exact (golden_not_prime_of_mod_five_eq_one_or_four hp h5 (Or.inl hone) hprime).elim
    · exact Or.inl htwo
    · exact Or.inr hthree
    · exact (golden_not_prime_of_mod_five_eq_one_or_four hp h5 (Or.inr hfour) hprime).elim
  · exact golden_prime_of_mod_five_eq_two_or_three hp

/-- Five is the square of the ramifying golden integer `-1 + 2 * phi`. -/
theorem golden_five_eq_ramified_square :
    (5 : GoldenInt) = (⟨-1, 2⟩ : GoldenInt) ^ 2 :=
  D5.S3.Arith.GoldenPrimeSplitting.golden_five_eq_ramified_square

end D5.S3.PrimeForms.GoldenPrimeClassification
