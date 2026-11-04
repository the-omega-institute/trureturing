/- GID: D5/S3/Arith/CharacterSums/ChenSunOriginal
   generality: I
   mirror-B: D5/B/S3/Arith/CharacterSums/ChenSunOriginal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Chen-Sun's all-prime four-branch congruence with the actual maximal-order class number. -/

import D5.S3.Arith.CharacterSums.ChenSunModSixteen
import D5.S3.Analytic.Zeta.QuadraticClassNumberSquare

namespace D5.S3.Arith.CharacterSums.ChenSunDoubleCharacter

open scoped BigOperators
open D5.S3.Arith.CharacterSums.QuadraticPrefixEnergy
open D5.S3.Arith.CharacterSums.QuadraticCharacterGram

open D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal

variable (p : ℕ) [Fact p.Prime]

/-- The p=5 mod8 branch of the original inclusive double sum. -/
theorem mod_eight_five (hp : p % 8 = 5) : Int.ModEq 16 (doubleSum p) (-2) := by
  let m := (p - 1) / 4
  have hpm : p = 4 * m + 1 := by dsimp only [m]; omega
  have hm : Odd (m : ℤ) := Int.odd_iff.mpr (by dsimp only [m]; omega)
  have hs : Int.ModEq 8 1 ((m : ℤ) ^ 2) :=
    Int.modEq_iff_dvd.mpr (Int.eight_dvd_sq_sub_one_of_odd hm)
  exact (even_doubleSum_mod16 p m hpm).trans (hs.symm.mul_left' (c := 2)).neg

/-- The p=1 mod8 branch, with the literal natural exponent (p-1)/8. -/
theorem mod_eight_one (hp : p % 8 = 1) :
    Int.ModEq 16 (doubleSum p) (4 * (1 - (-1 : ℤ) ^ ((p - 1) / 8))) := by
  let r := (p - 1) / 8
  have hpm : p = 4 * (2 * r) + 1 := by dsimp only [r]; omega
  have he := even_doubleSum_mod16 p (2 * r) hpm
  have ha : Int.ModEq 16 (-2 * ((2 * r : ℕ) : ℤ) ^ 2)
      (4 * (1 - (-1 : ℤ) ^ r)) := by
    rcases Nat.even_or_odd r with he | ho
    · rw [he.neg_one_pow]
      obtain ⟨t, ht⟩ := he
      have hr : r = 2 * t := by omega
      rw [hr]
      apply Int.modEq_iff_dvd.mpr
      refine ⟨2 * (t : ℤ) ^ 2, ?_⟩
      push_cast
      ring
    · rw [ho.neg_one_pow]
      obtain ⟨t, ht⟩ := ho
      have hr : r = 2 * t + 1 := by omega
      rw [hr]
      apply Int.modEq_iff_dvd.mpr
      refine ⟨2 * (t : ℤ) ^ 2 + 2 * t + 1, ?_⟩
      push_cast
      ring
  exact he.trans ha

section ActualClassNumber

variable [Fact (p % 4 = 3)]

/-- Here h is exactly the cardinality of the ideal class group of the ring of
integers of the proved quadratic number field, not a character-sum definition. -/
noncomputable abbrev imaginaryClassNumber : ℕ := NumberField.classNumber (PrimeImaginary.Field p)

private theorem excess_eq_partialSum :
    PrimeImaginary.quadraticExcess p = partialSum (fun j => legendreSym p (j : ℤ)) ((p - 1) / 2) := by
  rw [PrimeImaginary.quadraticExcess_eq_range, Finset.sum_range_succ']
  simp [partialSum]

private theorem odd_offset_three (m : ℕ) (hpm : p = 4 * m + 3) (hp8 : p % 8 = 3) :
    Int.ModEq 32 (4 * (m : ℤ) ^ 2 - 3) (2 * p - 9) := by
  have hm : Even m := Nat.even_iff.mpr (by omega)
  obtain ⟨r, hr⟩ := hm
  have hmr : m = 2 * r := by omega
  obtain ⟨t, ht⟩ := even_iff_two_dvd.mp (Int.even_mul_pred_self (r : ℤ))
  have hpz : (p : ℤ) = 4 * m + 3 := by exact_mod_cast hpm
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-t, ?_⟩
  rw [hpz, hmr]
  push_cast
  nlinarith [ht]

private theorem odd_offset_seven (m : ℕ) (hpm : p = 4 * m + 3) (hp8 : p % 8 = 7) :
    Int.ModEq 32 (4 * (m : ℤ) ^ 2 - 3) 1 := by
  have hm : Odd (m : ℤ) := Int.odd_iff.mpr (by omega)
  have h := Int.eight_dvd_sq_sub_one_of_odd hm
  obtain ⟨t, ht⟩ := h
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-t, ?_⟩
  nlinarith [ht]

/-- The p=3 mod8 branch uses the proved actual-class-number square and oddness. -/
theorem mod_eight_three (hp : 3 < p) (hp8 : p % 8 = 3) :
    Int.ModEq 16 (doubleSum p)
      ((p : ℤ) + 1 - (-1 : ℤ) ^ ((imaginaryClassNumber p - 1) / 2) * imaginaryClassNumber p) := by
  let m := (p - 3) / 4
  let h := imaginaryClassNumber p
  let s : ℤ := (-1) ^ ((h - 1) / 2)
  have hpm : p = 4 * m + 3 := by dsimp only [m]; omega
  have hn : (p - 1) / 2 = 2 * m + 1 := by omega
  have hc := PrimeImaginary.quadraticExcess_sq_classNumber p hp
  rw [excess_eq_partialSum, hn] at hc
  have hχ : legendreSym p 2 = -1 := by
    rw [legendreSym.at_two (by omega), ZMod.χ₈_nat_mod_eight p, hp8]
    rfl
  rw [hχ] at hc
  have hc' : partialSum (fun j => legendreSym p (j : ℤ)) (2 * m + 1) ^ 2 =
      9 * (h : ℤ) ^ 2 := by
    simpa only [h, imaginaryClassNumber, show (2 - -1 : ℤ) ^ 2 = 9 by norm_num] using hc
  have hh : Odd h := PrimeImaginary.classNumber_odd p hp
  have hhZ : Odd (h : ℤ) := by exact_mod_cast hh
  have hsquare : Int.ModEq 4 1 ((h : ℤ) ^ 2) := by
    change 1 % 4 = (h : ℤ) ^ 2 % 4
    rw [Int.sq_emod_four_eq_one_of_odd hhZ]
    norm_num
  have h9 : Int.ModEq 32 (9 * (h : ℤ) ^ 2) ((h : ℤ) ^ 2 + 8) := by
    have ht := (hsquare.symm.mul_left' (c := 8)).add_left ((h : ℤ) ^ 2)
    convert ht using 1 <;> ring
  have he := odd_doubleSum_mod32 p m hpm
  rw [hc'] at he
  have ht := h9.add (odd_offset_three p m hpm hp8)
  have hmid : Int.ModEq 32 (2 * doubleSum p) ((h : ℤ) ^ 2 + 2 * p - 1) := by
    apply he.trans
    convert ht using 1 <;> ring
  have hs := odd_sign_square_mod32 h hh
  have hs' := (hs.sub_right (2 * s * h)).add_right (2 * (p : ℤ) - 1)
  have hlast : Int.ModEq 32 ((h : ℤ) ^ 2 + 2 * p - 1)
      (2 * ((p : ℤ) + 1 - s * h)) := by
    convert hs' using 1 <;> dsimp only [s] <;> ring
  have hfinal := hmid.trans hlast
  exact Int.ModEq.mul_left_cancel' (c := 2) (m := 16) (by norm_num) hfinal

/-- The p=7 mod8 branch, with the same actual maximal-order class number. -/
theorem mod_eight_seven (hp : 3 < p) (hp8 : p % 8 = 7) :
    Int.ModEq 16 (doubleSum p)
      (2 - (-1 : ℤ) ^ ((imaginaryClassNumber p - 1) / 2) * imaginaryClassNumber p) := by
  let m := (p - 3) / 4
  let h := imaginaryClassNumber p
  let s : ℤ := (-1) ^ ((h - 1) / 2)
  have hpm : p = 4 * m + 3 := by dsimp only [m]; omega
  have hn : (p - 1) / 2 = 2 * m + 1 := by omega
  have hc := PrimeImaginary.quadraticExcess_sq_classNumber p hp
  rw [excess_eq_partialSum, hn] at hc
  have hχ : legendreSym p 2 = 1 := by
    rw [legendreSym.at_two (by omega), ZMod.χ₈_nat_mod_eight p, hp8]
    rfl
  rw [hχ] at hc
  have hc' : partialSum (fun j => legendreSym p (j : ℤ)) (2 * m + 1) ^ 2 =
      (h : ℤ) ^ 2 := by
    simpa only [h, imaginaryClassNumber, show (2 - 1 : ℤ) ^ 2 = 1 by norm_num,
      one_mul] using hc
  have he := odd_doubleSum_mod32 p m hpm
  rw [hc'] at he
  have hmid : Int.ModEq 32 (2 * doubleSum p) ((h : ℤ) ^ 2 + 1) := by
    apply he.trans
    convert (odd_offset_seven p m hpm hp8).add_left ((h : ℤ) ^ 2) using 1 <;> ring
  have hs := odd_sign_square_mod32 h (PrimeImaginary.classNumber_odd p hp)
  have hs' := (hs.sub_right (2 * s * h)).add_right 1
  have hlast : Int.ModEq 32 ((h : ℤ) ^ 2 + 1) (2 * (2 - s * h)) := by
    convert hs' using 1 <;> dsimp only [s] <;> ring
  have hfinal := hmid.trans hlast
  exact Int.ModEq.mul_left_cancel' (c := 2) (m := 16) (by norm_num) hfinal

end ActualClassNumber

/-- The four original residues. The final zero case is unreachable for primes p>3.
The class-number branches instantiate the proved field only when p=3 mod4. -/
noncomputable def originalResidue : ℤ :=
  if p % 8 = 1 then 4 * (1 - (-1 : ℤ) ^ ((p - 1) / 8)) else
  if p % 8 = 5 then -2 else
  if h4 : p % 4 = 3 then
    letI : Fact (p % 4 = 3) := ⟨h4⟩
    let h := imaginaryClassNumber p
    (if p % 8 = 3 then (p : ℤ) + 1 else 2) - (-1 : ℤ) ^ ((h - 1) / 2) * h
  else 0

/-- Chen-Sun arXiv:2409.08213v4 Conjecture 1.1(1.11), all primes p>3.
The double sum is literal (1.8); h in the two odd branches is NumberField.classNumber
of the maximal order of Q(sqrt(-p)), identified by PrimeImaginary.sqrtFieldEquiv and PrimeImaginary.maximalOrderEquiv. -/
theorem full_original (hp : 3 < p) : Int.ModEq 16 (doubleSum p) (originalResidue p) := by
  by_cases h1 : p % 8 = 1
  · simpa [originalResidue, h1] using mod_eight_one p h1
  by_cases h5 : p % 8 = 5
  · simpa [originalResidue, h1, h5] using mod_eight_five p h5
  have hpodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h4 : p % 4 = 3 := by have := Nat.odd_iff.mp hpodd; omega
  letI : Fact (p % 4 = 3) := ⟨h4⟩
  have hcases : p % 8 = 3 ∨ p % 8 = 7 := by omega
  rcases hcases with h3 | h7
  · simpa [originalResidue, h1, h5, h4, h3] using mod_eight_three p hp h3
  · simpa [originalResidue, h1, h5, h4, h7] using mod_eight_seven p hp h7

end D5.S3.Arith.CharacterSums.ChenSunDoubleCharacter
