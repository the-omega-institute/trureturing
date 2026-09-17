/- GID: D5/S1/Digit/Admissibility/WuDigitRangeSquareNotMultipleOfFive
   generality: I
   mirror-B: D5/B/S1/Digit/Admissibility/WuDigitRangeSquareNotMultipleOfFive
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Lemmas]
   utility: none
   digest: Decimal digit extrema five and nine for a number and its square exclude divisibility by five. -/
import Mathlib.Data.Nat.Digits.Lemmas

namespace D5.S1.Digit.Admissibility.WuDigitRangeSquareNotMultipleOfFive

/-- The decimal expansion has smallest digit five and largest digit nine. -/
def DigitRangeFiveNine (n : ℕ) : Prop :=
  (Nat.digits 10 n).min? = some 5 ∧ (Nat.digits 10 n).max? = some 9

/-- Chai Wah Wu's 2017 conjecture for OEIS A254074. -/
theorem result : ∀ k : ℕ, 0 < k → DigitRangeFiveNine k →
    DigitRangeFiveNine (k ^ 2) → ¬ (5 ∣ k) := by
  intro k hk hDigits hSquare hFive
  rw [DigitRangeFiveNine, List.min?_eq_some_iff, List.max?_eq_some_iff] at hDigits
  rw [DigitRangeFiveNine, List.min?_eq_some_iff, List.max?_eq_some_iff] at hSquare

  have hkDigits :
      Nat.digits 10 k = k % 10 :: Nat.digits 10 (k / 10) :=
    Nat.digits_def' (by norm_num) hk
  have hUnitsMem : k % 10 ∈ Nat.digits 10 k := by
    rw [hkDigits]
    simp
  have hUnitsLower : 5 ≤ k % 10 := hDigits.1.2 _ hUnitsMem
  have hkModFive : k % 5 = 0 := Nat.dvd_iff_mod_eq_zero.mp hFive
  have hNestedMod : k % 10 % 5 = k % 5 :=
    Nat.mod_mod_of_dvd k (by norm_num)
  have hkModTenLt : k % 10 < 10 := Nat.mod_lt k (by norm_num)
  have hkModTen : k % 10 = 5 := by omega

  have hNineTail : 9 ∈ Nat.digits 10 (k / 10) := by
    rw [hkDigits] at hDigits
    simpa [hkModTen] using hDigits.2.1
  have hQuotientNe : k / 10 ≠ 0 := by
    intro hZero
    simp [hZero] at hNineTail
  have hQuotientLower : 9 ≤ k / 10 := by
    by_contra hNot
    have hQuotientLt : k / 10 < 10 := by omega
    rw [Nat.digits_of_lt 10 (k / 10) hQuotientNe hQuotientLt] at hNineTail
    simp at hNineTail
    omega
  have hkRepr : k = 10 * (k / 10) + 5 := by
    have := Nat.mod_add_div k 10
    omega
  have hkLower : 59 ≤ k := by omega
  have hSquareLower : 100 ≤ k ^ 2 := by
    have hMul : 59 * 59 ≤ k * k := Nat.mul_le_mul hkLower hkLower
    norm_num [pow_two] at hMul ⊢
    omega

  have hSquareRepr :
      k ^ 2 = 100 * (k / 10) * (k / 10 + 1) + 25 := by
    conv_lhs => rw [hkRepr]
    ring
  have hSquareMod : k ^ 2 % 100 = 25 := by
    rw [hSquareRepr]
    simp [Nat.add_mod, Nat.mul_mod]
  have hTensValue : k ^ 2 / 10 % 10 = 2 := by
    calc
      k ^ 2 / 10 % 10 = k ^ 2 % (10 * 10) / 10 :=
        (Nat.mod_mul_right_div_self (k ^ 2) 10 10).symm
      _ = 2 := by norm_num [hSquareMod]
  have hTensGetD : (Nat.digits 10 (k ^ 2)).getD 1 0 = 2 := by
    calc
      (Nat.digits 10 (k ^ 2)).getD 1 0 = k ^ 2 / 10 ^ 1 % 10 :=
        Nat.getD_digits (k ^ 2) 1 (by norm_num)
      _ = 2 := by simpa using hTensValue
  have hTensIndex : 1 < (Nat.digits 10 (k ^ 2)).length := by
    apply (Nat.lt_digits_length_iff (b := 10) (k := 1) (by norm_num) (k ^ 2)).2
    norm_num
    omega
  have hTensEq : (Nat.digits 10 (k ^ 2))[1] = 2 := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hTensIndex] using hTensGetD
  have hTensMem : 2 ∈ Nat.digits 10 (k ^ 2) := by
    have hMem := List.getElem_mem hTensIndex
    simpa [hTensEq] using hMem
  have := hSquare.1.2 2 hTensMem
  omega

#print axioms DigitRangeFiveNine
#print axioms result

end D5.S1.Digit.Admissibility.WuDigitRangeSquareNotMultipleOfFive
