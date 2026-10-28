/- GID: D5/S1/Recurrence/Residue/TebniA341724RowDivisibility
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/TebniA341724RowDivisibility
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Prime and dyadic row divisibility for the original A341724 column EGF. -/

import D5.S1.Recurrence.Residue.TebniA364822PowerOfTwo

set_option autoImplicit false

namespace D5.S1.Recurrence.Residue.TebniA341724RowDivisibility

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Residue.TebniA364822 (sinh eCoeff_sinh)

/-- The denominator `1 - 2 sinh(-X)` of the original column EGF. -/
noncomputable def denominator : ℚ⟦X⟧ := 1 - 2 * rescale (-1) sinh

/-- The literal rational formal column `X^k / (k! (1 - 2 sinh(-X)))`. -/
noncomputable def column (k : ℕ) : ℚ⟦X⟧ :=
  X ^ k * (C ((k.factorial : ℚ)⁻¹) * denominator⁻¹)

/-- The factorial-normalized coefficients of the original OEIS columns. -/
noncomputable def Tq (n k : ℕ) : ℚ := eCoeff (column k) n

/-- Both row-divisibility conjectures, including integer witnesses. -/
def claim : Prop :=
  (∀ p k : ℕ, Nat.Prime p → 0 < k → k < p →
    ∃ z : ℤ, (z : ℚ) = Tq p k ∧ (p : ℤ) ∣ z) ∧
  (∀ m k : ℕ, k < 2 ^ m →
    ∃ z : ℤ, (z : ℚ) = Tq (2 ^ m) k ∧ ((2 ^ m : ℕ) : ℤ) ∣ z)

private theorem sinh_neg : rescale (-1) sinh = -sinh := by
  ext n
  apply mul_left_cancel₀ (show (n.factorial : ℚ) ≠ 0 by exact_mod_cast n.factorial_ne_zero)
  calc
    (n.factorial : ℚ) * coeff n (rescale (-1) sinh) =
        (-1 : ℚ) ^ n * eCoeff sinh n := by
      simp only [coeff_rescale, eCoeff]
      ring
    _ = - eCoeff sinh n := by
      rw [eCoeff_sinh]
      by_cases he : Even n
      · simp [he]
      · simp [he, (Nat.not_even_iff_odd.mp he).neg_one_pow]
    _ = (n.factorial : ℚ) * coeff n (-sinh) := by simp [eCoeff]

private theorem denominator_eq : denominator = 1 + 2 * sinh := by
  simp [denominator, sinh_neg]

private theorem denominator_zero : constantCoeff denominator = 1 := by
  have hs : constantCoeff sinh = 0 := by simpa using eCoeff_sinh 0
  simp [denominator_eq, hs]

private theorem support (n k : ℕ) (h : n < k) : Tq n k = 0 := by
  simp [Tq, eCoeff, column, coeff_X_pow_mul', Nat.not_le.mpr h]

private theorem diagonal (k : ℕ) : Tq k k = 1 := by
  simp [Tq, eCoeff, column, coeff_X_pow_mul', coeff_zero_eq_constantCoeff,
    denominator_zero, Nat.factorial_ne_zero]

private theorem forcing (n k : ℕ) :
    eCoeff (X ^ k * C ((k.factorial : ℚ)⁻¹)) n = if n = k then 1 else 0 := by
  rw [mul_comm (X ^ k)]
  simp only [eCoeff, coeff_C_mul, coeff_X_pow]
  by_cases h : n = k
  · subst n
    simp [Nat.factorial_ne_zero]
  · simp [h, Ne.symm h]

private theorem recurrence (n k : ℕ) : Tq n k = (if n = k then 1 else 0) -
    2 * ∑ j ∈ range n, (n.choose (j + 1) : ℚ) *
      (if Even (j + 1) then 0 else 1) * Tq (n - (j + 1)) k := by
  have hm : column k * denominator = X ^ k * C ((k.factorial : ℚ)⁻¹) := by
    simp only [column, mul_assoc]
    rw [PowerSeries.inv_mul_cancel _ (by rw [denominator_zero]; norm_num), mul_one]
  have hf : column k = X ^ k * C ((k.factorial : ℚ)⁻¹) - 2 * (sinh * column k) := by
    rw [denominator_eq] at hm
    linear_combination hm
  change eCoeff (column k) n = _
  rw [hf]
  calc
    eCoeff (X ^ k * C ((k.factorial : ℚ)⁻¹) - 2 * (sinh * column k)) n =
        eCoeff (X ^ k * C ((k.factorial : ℚ)⁻¹)) n -
          2 * eCoeff (sinh * column k) n := by
      simp only [eCoeff, map_sub, coeff_ofNat_mul]
      ring
    _ = _ := by
      rw [forcing, eCoeff_mul, sum_range_succ']
      simp only [eCoeff_sinh, Tq, even_zero, if_true, mul_zero, zero_mul, add_zero]

private theorem column_integral (k : ℕ) : Integral (column k) := by
  intro n
  change ∃ z : ℤ, Tq n k = (z : ℚ)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hnk : n ≤ k
    · by_cases he : n = k
      · subst n
        exact ⟨1, by simpa using diagonal k⟩
      · exact ⟨0, by simpa using support n k (by omega)⟩
    · have hz (j : ℕ) (hj : j < n) : ((Tq j k).num : ℚ) = Tq j k := by
        obtain ⟨z, he⟩ := ih j hj
        simp [he]
      refine ⟨-2 * ∑ j ∈ range n, (n.choose (j + 1) : ℤ) *
        (if Even (j + 1) then 0 else 1) * (Tq (n - (j + 1)) k).num, ?_⟩
      rw [recurrence, if_neg (by omega), zero_sub]
      simp only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_sum,
        Int.cast_natCast, Int.cast_ite, Int.cast_zero, Int.cast_one, neg_mul]
      congr 1
      apply sum_congr rfl
      intro j hj
      rw [hz _ (by have := mem_range.mp hj; omega)]

private theorem num_cast (n k : ℕ) : ((Tq n k).num : ℚ) = Tq n k := by
  obtain ⟨z, hz⟩ := column_integral k n
  change Tq n k = (z : ℚ) at hz
  simp [hz]

private theorem num_recurrence (n k : ℕ) : (Tq n k).num =
    (if n = k then 1 else 0) - 2 * ∑ j ∈ range n,
      (n.choose (j + 1) : ℤ) * (if Even (j + 1) then 0 else 1) *
        (Tq (n - (j + 1)) k).num := by
  apply Int.cast_injective (α := ℚ)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat,
    Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_natCast, num_cast]
  exact recurrence n k

/-- Both original A341724 conjectures hold for their exact rational EGF. -/
theorem result : claim := by
  constructor
  · intro p k hp hk hkp
    refine ⟨(Tq p k).num, num_cast p k, ?_⟩
    rw [num_recurrence, if_neg (by omega), zero_sub]
    apply dvd_neg.mpr
    apply dvd_mul_of_dvd_right
    apply Finset.dvd_sum
    intro j hj
    by_cases he : Even (j + 1)
    · simp [he]
    · by_cases hjp : j + 1 = p
      · simp [hjp, support 0 k hk]
      · have hd : p ∣ p.choose (j + 1) :=
          hp.dvd_choose_self (by omega) (by have := mem_range.mp hj; omega)
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hd) _) _
  · intro m k hk
    refine ⟨(Tq (2 ^ m) k).num, num_cast (2 ^ m) k, ?_⟩
    rw [num_recurrence, if_neg (by omega), zero_sub]
    apply dvd_neg.mpr
    apply dvd_mul_of_dvd_right
    apply Finset.dvd_sum
    intro j hj
    by_cases he : Even (j + 1)
    · simp [he]
    · have hd := TebniA364822PowerOfTwo.pow_two_dvd_choose_odd m (j + 1)
        (Nat.not_even_iff_odd.mp he)
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hd) _) _

end D5.S1.Recurrence.Residue.TebniA341724RowDivisibility
