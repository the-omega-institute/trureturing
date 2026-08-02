/- GID: D5/S3/Arith/GoldenSplitSufficient
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: p=pm1 mod5 primes split in golden integers, completing the splitting law. -/

import D5.S3.Arith.GoldenPrimeSplitting
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace D5.S3.Arith.GoldenSplitSufficient

open D5.S0.Carrier
open D5.S3.Arith.GoldenPrimeSplitting

private theorem five_is_square_mod_prime_of_mod_five_eq_one_or_four
    {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5)
    (hmod : p % 5 = 1 ∨ p % 5 = 4) : IsSquare (5 : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hp5ne : (p : ZMod 5) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hdiv
    exact h5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp hdiv).symm
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
  have hpneTwo : p ≠ 2 := by
    intro h
    subst p
    norm_num at hmod
  have hlegendreFive : legendreSym p 5 = 1 := by
    calc
      legendreSym p 5 = legendreSym 5 p :=
        legendreSym.quadratic_reciprocity_one_mod_four
          (p := 5) (q := p) (by norm_num) hpneTwo
      _ = 1 := hlegendreP
  have hfiveNe : (5 : ZMod p) ≠ 0 := by
    change ((5 : ℕ) : ZMod p) ≠ 0
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hdiv
    exact h5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hdiv)
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
  have hfiveSquare := five_is_square_mod_prime_of_mod_five_eq_one_or_four hp h5 hmod
  have hpneTwo : p ≠ 2 := by
    intro h
    subst p
    norm_num at hmod
  rcases golden_polynomial_has_root_of_five_is_square hp hpneTwo hfiveSquare with ⟨r, hr⟩
  exact golden_not_prime_of_polynomial_root hp r hr

end D5.S3.Arith.GoldenSplitSufficient
