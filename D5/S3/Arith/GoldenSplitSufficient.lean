/- GID: D5/S3/Arith/GoldenSplitSufficient
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenSplitSufficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: p=pm1 mod5 primes split in golden integers, completing the splitting law. -/

import D5.S3.Arith.GoldenPrimeSplitting
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace D5.S3.Arith.GoldenSplitSufficient

open D5.S0.Carrier
open D5.S3.Arith.GoldenPrimeSplitting

private theorem zmod_five_nonzero_square_eq_one_or_four
    (z : ZMod 5) (hz : z ≠ 0) (hsquare : IsSquare z) : z = 1 ∨ z = 4 := by
  revert z
  decide

/-- For a prime other than five, five is a square modulo that prime exactly
when the prime is congruent to one or minus one modulo five. -/
theorem five_is_square_mod_prime_iff_mod_five_eq_one_or_four
    {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) (h2 : p ≠ 2)
    : IsSquare (5 : ZMod p) ↔ p % 5 = 1 ∨ p % 5 = 4 := by
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

private theorem golden_polynomial_has_root_of_five_is_square
    {p : ℕ} (hp : p.Prime) (hpneTwo : p ≠ 2)
    (hfiveSquare : IsSquare (5 : ZMod p)) :
    ∃ r : ZMod p, r ^ 2 - r - 1 = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases hfiveSquare with ⟨s, hs⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hdiv
    exact hpneTwo ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdiv)
  have hfour : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]
    exact mul_ne_zero htwo htwo
  refine ⟨(1 + s) / 2, ?_⟩
  calc
    ((1 + s) / 2) ^ 2 - (1 + s) / 2 - 1 = (s * s - 5) / 4 := by
      field_simp [htwo, hfour]
      ring
    _ = 0 := by rw [← hs]; simp

private theorem golden_not_prime_of_polynomial_root
    {p : ℕ} (hp : p.Prime) (r : ZMod p) (hr : r ^ 2 - r - 1 = 0) :
    ¬ Prime (p : GoldenInt) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let g : GoldenInt := ⟨-(r.val : ℤ), 1⟩
  have hnormCast : ((norm g : ℤ) : ZMod p) = 0 := by
    rw [show norm g = (r.val : ℤ) ^ 2 - r.val - 1 by
      simp [g, D5.S0.Carrier.norm]
      ring]
    have hval : (r.val : ZMod p) = r := ZMod.natCast_zmod_val r
    simpa [hval, pow_two] using hr
  have hnormDvd : (p : ℤ) ∣ norm g :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (norm g) p).mp hnormCast
  rcases hnormDvd with ⟨k, hk⟩
  have hproductDvd : (p : GoldenInt) ∣ g * conj g := by
    refine ⟨(k : GoldenInt), ?_⟩
    rw [← norm_eq_mul_conj]
    simp [hk, mul_comm]
  have hpNotDvdG : ¬ (p : GoldenInt) ∣ g := by
    rintro ⟨q, hq⟩
    have hb := congrArg GoldenInt.b hq
    have hpDvdOne : (p : ℤ) ∣ 1 := by
      refine ⟨q.b, ?_⟩
      simpa [g] using hb
    exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp hpDvdOne)
  have hpNotDvdConj : ¬ (p : GoldenInt) ∣ conj g := by
    rintro ⟨q, hq⟩
    have hb := congrArg GoldenInt.b hq
    have hpDvdOne : (p : ℤ) ∣ 1 := by
      refine ⟨-q.b, ?_⟩
      have hneg := congrArg Neg.neg hb
      simpa [g, conj] using hneg
    exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp hpDvdOne)
  let d : GoldenInt := EuclideanDomain.gcd (p : GoldenInt) g
  rcases EuclideanDomain.gcd_dvd_left (p : GoldenInt) g with ⟨c, hfactor⟩
  have hdNotUnit : ¬ IsUnit d := by
    intro hd
    have hrel : IsRelPrime (p : GoldenInt) g := by
      intro z hzp hzg
      exact isUnit_of_dvd_unit (EuclideanDomain.dvd_gcd hzp hzg) (by simpa [d] using hd)
    exact hpNotDvdConj (hrel.dvd_of_dvd_mul_left hproductDvd)
  have hcNotUnit : ¬ IsUnit c := by
    intro hc
    apply hpNotDvdG
    have hassociated : Associated (p : GoldenInt) d := by
      rw [hfactor]
      exact associated_mul_unit_left d c hc
    exact hassociated.dvd.trans (by
      simpa [d] using EuclideanDomain.gcd_dvd_right (p : GoldenInt) g)
  intro hprime
  have hirr : Irreducible (p : GoldenInt) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mpr hprime
  exact (hirr.isUnit_or_isUnit hfactor).elim hdNotUnit hcNotUnit

/-- A rational prime congruent to `1` or `-1` modulo five splits, in the
sense that its image in the golden integers is not a prime element. -/
theorem golden_not_prime_of_mod_five_eq_one_or_four {p : ℕ} (hp : p.Prime)
    (h5 : p ≠ 5) (hmod : p % 5 = 1 ∨ p % 5 = 4) :
    ¬ Prime (p : GoldenInt) := by
  have hpneTwo : p ≠ 2 := by
    intro h
    subst p
    norm_num at hmod
  have hfiveSquare :=
    (five_is_square_mod_prime_iff_mod_five_eq_one_or_four hp h5 hpneTwo).2 hmod
  rcases golden_polynomial_has_root_of_five_is_square hp hpneTwo hfiveSquare with ⟨r, hr⟩
  exact golden_not_prime_of_polynomial_root hp r hr

/-- A prime other than five splits in the golden integers exactly in the two
square residue classes modulo five. Here splitting is expressed by failure of
the rational prime to remain a prime element. -/
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

end D5.S3.Arith.GoldenSplitSufficient
