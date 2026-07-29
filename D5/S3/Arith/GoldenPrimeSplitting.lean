/- GID: D5/S3/Arith/GoldenPrimeSplitting
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Inert rational primes in the golden integers. -/

import D5.S0.Carrier.PrincipalIdeal
import D5.S0.Carrier.Units
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

namespace D5.S3.Arith.GoldenPrimeSplitting

open D5.S0.Carrier

private theorem zmod_five_golden_norm (a b : ZMod 5) :
    a * a + a * b - b * b = 0 ∨ a * a + a * b - b * b = 1 ∨
      a * a + a * b - b * b = 4 := by
  revert a b
  decide

private theorem zmod_five_good_not_bad (z : ZMod 5)
    (hgood : z = 0 ∨ z = 1 ∨ z = 4) (hbad : z = 2 ∨ z = 3) : False := by
  have hvalZero : (0 : ZMod 5).val = 0 := by decide
  have hvalOne : (1 : ZMod 5).val = 1 := by decide
  have hvalTwo : (2 : ZMod 5).val = 2 := by decide
  have hvalThree : (3 : ZMod 5).val = 3 := by decide
  have hvalFour : (4 : ZMod 5).val = 4 := by decide
  have hgoodVal : z.val = 0 ∨ z.val = 1 ∨ z.val = 4 := by
    rcases hgood with hzero | hone | hfour
    · exact Or.inl ((congrArg ZMod.val hzero).trans hvalZero)
    · exact Or.inr (Or.inl ((congrArg ZMod.val hone).trans hvalOne))
    · exact Or.inr (Or.inr ((congrArg ZMod.val hfour).trans hvalFour))
  have hbadVal : z.val = 2 ∨ z.val = 3 := by
    rcases hbad with htwo | hthree
    · exact Or.inl ((congrArg ZMod.val htwo).trans hvalTwo)
    · exact Or.inr ((congrArg ZMod.val hthree).trans hvalThree)
  omega

private theorem zmod_five_neg_bad (z : ZMod 5) (hbad : z = 2 ∨ z = 3) :
    -z = 2 ∨ -z = 3 := by
  rcases hbad with rfl | rfl
  · exact Or.inr (by decide)
  · exact Or.inl (by decide)

/-- Every golden norm is zero or a square class modulo five. -/
theorem golden_norm_zmod_five (x : GoldenInt) :
    ((norm x : ℤ) : ZMod 5) = 0 ∨ ((norm x : ℤ) : ZMod 5) = 1 ∨
      ((norm x : ℤ) : ZMod 5) = 4 := by
  simpa [norm] using zmod_five_golden_norm (x.a : ZMod 5) (x.b : ZMod 5)

/-- Integers in the two nonsquare classes modulo five are not absolute golden
norms. -/
theorem golden_no_norm_natAbs_of_mod_five_eq_two_or_three {n : ℕ}
    (hmod : n % 5 = 2 ∨ n % 5 = 3) (x : GoldenInt) : (norm x).natAbs ≠ n := by
  intro habs
  have hnCast : (n : ZMod 5) = 2 ∨ (n : ZMod 5) = 3 := by
    rcases hmod with hmod | hmod
    · left
      rw [← ZMod.natCast_mod n 5, hmod]
      norm_num
    · right
      rw [← ZMod.natCast_mod n 5, hmod]
      norm_num
  rcases Int.natAbs_eq (norm x) with hpos | hneg
  · rw [habs] at hpos
    apply zmod_five_good_not_bad ((norm x : ℤ) : ZMod 5) (golden_norm_zmod_five x)
    simpa [hpos] using hnCast
  · rw [habs] at hneg
    apply zmod_five_good_not_bad ((norm x : ℤ) : ZMod 5) (golden_norm_zmod_five x)
    simpa [hneg] using zmod_five_neg_bad (n : ZMod 5) hnCast

/-- The necessary half of the prime norm-representation law: a represented
prime is ramified or lies in one of the two split residue classes. -/
theorem golden_prime_norm_representation_only_if {p : ℕ} (hp : p.Prime)
    (hrep : ∃ x : GoldenInt, (norm x).natAbs = p) :
    p = 5 ∨ p % 5 = 1 ∨ p % 5 = 4 := by
  rcases hrep with ⟨x, hx⟩
  have hlt : p % 5 < 5 := Nat.mod_lt p (by norm_num)
  have hclasses :
      p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
    omega
  rcases hclasses with hzero | hone | htwo | hthree | hfour
  · left
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp
      (Nat.dvd_of_mod_eq_zero hzero)).symm
  · exact Or.inr (Or.inl hone)
  · exact (golden_no_norm_natAbs_of_mod_five_eq_two_or_three (Or.inl htwo) x hx).elim
  · exact (golden_no_norm_natAbs_of_mod_five_eq_two_or_three (Or.inr hthree) x hx).elim
  · exact Or.inr (Or.inr hfour)

/-- A rational prime in either nonsquare class modulo five is inert in the
golden integer ring. -/
theorem golden_prime_of_mod_five_eq_two_or_three {p : ℕ} (hp : p.Prime)
    (hmod : p % 5 = 2 ∨ p % 5 = 3) : Prime (p : GoldenInt) := by
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  refine ⟨?_, ?_⟩
  · rw [isUnit_iff_norm_natAbs_eq_one]
    simp [norm, Int.natAbs_mul, hp.ne_one]
  · intro a b hab
    by_contra hunits
    rw [not_or] at hunits
    have haOne : (norm a).natAbs ≠ 1 := by
      intro ha
      exact hunits.1 ((isUnit_iff_norm_natAbs_eq_one a).mpr ha)
    have hbOne : (norm b).natAbs ≠ 1 := by
      intro hb
      exact hunits.2 ((isUnit_iff_norm_natAbs_eq_one b).mpr hb)
    have hnorm : norm (p : GoldenInt) = norm a * norm b := by
      rw [hab, norm_mul]
    have hnormAbs := congrArg Int.natAbs hnorm
    have hproduct : (norm a).natAbs * (norm b).natAbs = p ^ 2 := by
      simpa [norm, Int.natAbs_mul, pow_two] using hnormAbs.symm
    have habs := (hp.mul_eq_prime_sq_iff haOne hbOne).mp hproduct
    exact golden_no_norm_natAbs_of_mod_five_eq_two_or_three hmod a habs.1

/-- The ramified rational prime five is represented by the golden norm. -/
theorem golden_norm_represents_five : ∃ x : GoldenInt, (norm x).natAbs = 5 := by
  exact ⟨⟨1, 3⟩, by norm_num [norm]⟩

/-- Five is the square of the ramifying golden integer `-1 + 2 * phi`. -/
theorem golden_five_eq_ramified_square :
    (5 : GoldenInt) = (⟨-1, 2⟩ : GoldenInt) ^ 2 := by
  decide

/-- The rational prime five is not a prime element of the golden integers. -/
theorem golden_five_not_prime : ¬ Prime (5 : GoldenInt) := by
  intro hprime
  have hirr : Irreducible (5 : GoldenInt) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mpr hprime
  have hfactor : (5 : GoldenInt) = (⟨-1, 2⟩ : GoldenInt) * ⟨-1, 2⟩ := by
    decide
  have hunits := hirr.isUnit_or_isUnit hfactor
  have hnotUnit : ¬ IsUnit (⟨-1, 2⟩ : GoldenInt) := by
    rw [isUnit_iff_norm_natAbs_eq_one]
    norm_num [norm]
  exact hunits.elim hnotUnit hnotUnit

/-- Eleven, congruent to one modulo five, is represented by the golden norm. -/
theorem golden_norm_represents_eleven : ∃ x : GoldenInt, (norm x).natAbs = 11 := by
  exact ⟨⟨3, 1⟩, by norm_num [norm]⟩

/-- Nineteen, congruent to minus one modulo five, is represented by the golden norm. -/
theorem golden_norm_represents_nineteen : ∃ x : GoldenInt, (norm x).natAbs = 19 := by
  exact ⟨⟨4, 1⟩, by norm_num [norm]⟩

/-- Two stays prime in the golden integer ring. -/
theorem golden_prime_two : Prime (2 : GoldenInt) := by
  apply golden_prime_of_mod_five_eq_two_or_three Nat.prime_two
  norm_num

/-- Three stays prime in the golden integer ring. -/
theorem golden_prime_three : Prime (3 : GoldenInt) := by
  apply golden_prime_of_mod_five_eq_two_or_three Nat.prime_three
  norm_num

end D5.S3.Arith.GoldenPrimeSplitting
