/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207LeftRational
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207LeftRational
   mirror-E: none(waiver:formal-rational-lambert-support)
   anchors: []
   utility: none
   digest: Laurent support induction constructs the convergent rational Lambert moment. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftNormalization
import D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftDiagonal
import D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftGauge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftMoment

open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology
open InversionSeq207LeftNormalization InversionSeq207LeftDiagonal
open InversionSeq207LeftGauge InversionSeq207Catalytic

noncomputable def leftRationalNumerator : PowerSeries (LaurentPolynomial ℚ) :=
  let denominator : PowerSeries (LaurentPolynomial ℚ) :=
    1 + PowerSeries.X * PowerSeries.C (LaurentPolynomial.T (-1) - 2) +
      PowerSeries.X ^ 2 * PowerSeries.C (LaurentPolynomial.T 1 - 2) + PowerSeries.X ^ 3
  (PowerSeries.X - 1) ^ 3 * (PowerSeries.X + 1) ^ 3 *
    PowerSeries.C ((LaurentPolynomial.T 1 - 1) ^ 2) *
    (PowerSeries.X * PowerSeries.C (LaurentPolynomial.T 1) - 1) ^ 2 *
    (PowerSeries.X * PowerSeries.C (LaurentPolynomial.T 2) - 1) *
    PowerSeries.C (LaurentPolynomial.T (-3)) * PowerSeries.invOfUnit denominator 1

noncomputable def leftLambertSum : PowerSeries ℚ :=
  PowerSeries.mk fun degree =>
    ∑ index ∈ Finset.range (degree + 4),
      if index = 0 then 0 else
        -(index : ℚ) ^ 2 * PowerSeries.coeff degree
          (PowerSeries.mk (fun earlier =>
            (PowerSeries.coeff earlier leftRationalNumerator).coeff index) *
            PowerSeries.invOfUnit (1 - PowerSeries.X ^ index) 1)

noncomputable def leftScalarMoment : PowerSeries ℚ :=
  PowerSeries.invOfUnit ((1 - PowerSeries.X) ^ 4) 1 *
    PowerSeries.mk fun degree => PowerSeries.coeff (degree + 1) leftLambertSum

set_option maxHeartbeats 6400000 in
theorem left_rational_regularity :
    (let q : PowerSeries (LaurentPolynomial ℚ) := PowerSeries.X
     (1 + q * PowerSeries.C (LaurentPolynomial.T (-1) - 2) +
       q ^ 2 * PowerSeries.C (LaurentPolynomial.T 1 - 2) + q ^ 3) *
         leftRationalNumerator =
       (q - 1) ^ 3 * (q + 1) ^ 3 * PowerSeries.C ((LaurentPolynomial.T 1 - 1) ^ 2) *
         (q * PowerSeries.C (LaurentPolynomial.T 1) - 1) ^ 2 *
         (q * PowerSeries.C (LaurentPolynomial.T 2) - 1) *
         PowerSeries.C (LaurentPolynomial.T (-3))) ∧
    (∀ degree : ℕ, ∀ index : ℤ, (degree : ℤ) + 3 < |index| →
      (PowerSeries.coeff degree leftRationalNumerator).coeff index = 0) ∧
    (letI : UniformSpace ℚ := ⊥
     letI : DiscreteUniformity ℚ := ⟨rfl⟩
     HasSum (fun index : ℕ => if index = 0 then 0 else
       PowerSeries.C (-(index : ℚ) ^ 2) *
         PowerSeries.mk (fun degree =>
           (PowerSeries.coeff degree leftRationalNumerator).coeff index) *
         PowerSeries.invOfUnit (1 - PowerSeries.X ^ index) 1) leftLambertSum) ∧
    ((1 - PowerSeries.X) ^ 4 * (PowerSeries.X * leftScalarMoment) = leftLambertSum) := by
  classical
  let denominator : PowerSeries (LaurentPolynomial ℚ) :=
    1 + PowerSeries.X * PowerSeries.C (LaurentPolynomial.T (-1) - 2) +
      PowerSeries.X ^ 2 * PowerSeries.C (LaurentPolynomial.T 1 - 2) + PowerSeries.X ^ 3
  let inverse := PowerSeries.invOfUnit denominator 1
  have honeCoeff (index : ℤ) (hne : index ≠ 0) :
      (1 : LaurentPolynomial ℚ).coeff index = 0 := by
    change (Finsupp.single 0 (1 : ℚ)) index = 0
    simp only [Finsupp.single_apply, if_neg (Ne.symm hne)]
  have hpolyProduct (left right : LaurentPolynomial ℚ)
      (lowerLeft upperLeft lowerRight upperRight : ℤ)
      (hleft : ∀ index, index < lowerLeft ∨ upperLeft < index → left.coeff index = 0)
      (hright : ∀ index, index < lowerRight ∨ upperRight < index → right.coeff index = 0) :
      ∀ index, index < lowerLeft + lowerRight ∨ upperLeft + upperRight < index →
        (left * right).coeff index = 0 := by
    intro index hindex
    rw [AddMonoidAlgebra.coeff_mul_apply_left]
    unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro first _
    dsimp only
    by_cases hfirst : first < lowerLeft ∨ upperLeft < first
    · rw [hleft first hfirst, zero_mul]
    · rw [hright (-first + index) (by omega), mul_zero]
  have hproduct (left right : PowerSeries (LaurentPolynomial ℚ))
      (lowerLeft upperLeft lowerRight upperRight : ℤ)
      (hleft : ∀ degree index, index < lowerLeft ∨ upperLeft < index →
        (PowerSeries.coeff degree left).coeff index = 0)
      (hright : ∀ degree index, index < lowerRight ∨ upperRight < index →
        (PowerSeries.coeff degree right).coeff index = 0) :
      ∀ degree index, index < lowerLeft + lowerRight ∨ upperLeft + upperRight < index →
        (PowerSeries.coeff degree (left * right)).coeff index = 0 := by
    intro degree index hindex
    simp only [PowerSeries.coeff_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro pair _
    exact hpolyProduct _ _ _ _ _ _ (hleft pair.1) (hright pair.2) index hindex
  have hpower (series : PowerSeries (LaurentPolynomial ℚ)) (lower upper : ℤ)
      (hseries : ∀ degree index, index < lower ∨ upper < index →
        (PowerSeries.coeff degree series).coeff index = 0) :
      ∀ (power degree : ℕ) (index : ℤ),
        index < (power : ℤ) * lower ∨ (power : ℤ) * upper < index →
        (PowerSeries.coeff degree (series ^ power)).coeff index = 0 := by
    intro power
    induction power with
    | zero =>
        intro degree index hindex
        have hzero : index ≠ 0 := by omega
        simp only [pow_zero, PowerSeries.coeff_one]
        split_ifs
        · exact honeCoeff index hzero
        · rfl
    | succ power ih =>
        simpa only [pow_succ, Nat.cast_succ, add_mul, one_mul] using
          hproduct (series ^ power) series ((power : ℤ) * lower)
            ((power : ℤ) * upper) lower upper ih hseries
  have hdenominator (degree : ℕ) : PowerSeries.coeff degree denominator =
      (if degree = 0 then 1 else 0) +
      (if degree = 1 then LaurentPolynomial.T (-1) - 2 else 0) +
      (if degree = 2 then LaurentPolynomial.T 1 - 2 else 0) +
      (if degree = 3 then 1 else 0) := by
    simp only [denominator, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
    congr 2
    · rw [mul_comm, ← pow_one (PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)),
        PowerSeries.coeff_C_mul_X_pow]
    · rw [mul_comm, PowerSeries.coeff_C_mul_X_pow]
  have hdenSupport (degree : ℕ) (index : ℤ) (hlarge : (degree : ℤ) < |index|) :
      (PowerSeries.coeff degree denominator).coeff index = 0 := by
    simp only [lt_abs] at hlarge
    rw [hdenominator]
    by_cases hzero : degree = 0
    · subst degree
      have hindex : index ≠ 0 := by omega
      simpa using honeCoeff index hindex
    by_cases hone : degree = 1
    · subst degree
      have hindex : index ≠ 0 := by omega
      have hminus : (-1 : ℤ) ≠ index := by omega
      simp [hindex, hminus]
    by_cases htwo : degree = 2
    · subst degree
      have hindex : index ≠ 0 := by omega
      have hplus : (1 : ℤ) ≠ index := by omega
      simp [hindex, hplus]
    by_cases hthree : degree = 3
    · subst degree
      have hindex : index ≠ 0 := by omega
      simpa using honeCoeff index hindex
    simp [hzero, hone, htwo, hthree]
  have hinverse : ∀ degree : ℕ, ∀ index : ℤ, (degree : ℤ) < |index| →
      (PowerSeries.coeff degree inverse).coeff index = 0 := by
    intro degree
    induction degree using Nat.strong_induction_on with
    | h degree ih =>
        intro index hindex
        simp only [lt_abs] at hindex
        rw [show inverse = PowerSeries.invOfUnit denominator 1 from rfl,
          PowerSeries.coeff_invOfUnit]
        by_cases hzero : degree = 0
        · subst degree
          have hne : index ≠ 0 := by omega
          simpa using honeCoeff index hne
        simp only [if_neg hzero, inv_one, Units.val_one, neg_one_mul,
          AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, AddMonoidAlgebra.coeff_sum]
        rw [neg_eq_zero]
        simp only [Finsupp.finsetSum_apply]
        apply Finset.sum_eq_zero
        intro pair hpair
        have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
        by_cases hless : pair.2 < degree
        · simp only [if_pos hless]
          apply hpolyProduct _ _ (-(pair.1 : ℤ)) pair.1 (-(pair.2 : ℤ)) pair.2
          · intro exponent hexponent
            exact hdenSupport pair.1 exponent (by simp only [lt_abs]; omega)
          · intro exponent hexponent
            exact ih pair.2 hless exponent (by simp only [lt_abs]; omega)
          · omega
        · simp [hless]
  have hscalar (series : PowerSeries ℚ) :
      ∀ degree index, index < (0 : ℤ) ∨ 0 < index →
        (PowerSeries.coeff degree (PowerSeries.map LaurentPolynomial.C series)).coeff index =
          0 := by
    intro degree index hindex
    rw [PowerSeries.coeff_map]
    change (LaurentPolynomial.C _).coeff index = 0
    simp [show index ≠ 0 by omega]
  have hconstant (value : LaurentPolynomial ℚ) (lower upper : ℤ)
      (hvalue : ∀ index, index < lower ∨ upper < index → value.coeff index = 0) :
      ∀ degree index, index < lower ∨ upper < index →
        (PowerSeries.coeff degree (PowerSeries.C value)).coeff index = 0 := by
    intro degree index hindex
    rw [PowerSeries.coeff_C]
    split_ifs
    · exact hvalue index hindex
    · rfl
  have hlinear (exponent : ℤ) (hpositive : 0 ≤ exponent) :
      ∀ (degree : ℕ) (index : ℤ), index < (0 : ℤ) ∨ exponent < index →
        (PowerSeries.coeff degree
          (PowerSeries.X * PowerSeries.C (LaurentPolynomial.T exponent) -
            (1 : PowerSeries (LaurentPolynomial ℚ)))).coeff index =
            0 := by
    intro degree index hindex
    have hzero : index ≠ 0 := by omega
    have hexponent : exponent ≠ index := by omega
    rw [map_sub, mul_comm, ← pow_one (PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)),
      PowerSeries.coeff_C_mul_X_pow]
    simp only [PowerSeries.coeff_one]
    split_ifs <;> simp [hexponent, honeCoeff index hzero]
  have hfirst : ∀ degree index, index < (0 : ℤ) ∨ 2 < index →
      (PowerSeries.coeff degree
        (PowerSeries.C ((LaurentPolynomial.T (1 : ℤ) -
          (1 : LaurentPolynomial ℚ)) ^ 2))).coeff index = 0 := by
    apply hconstant _ 0 2
    have hbase : ∀ index : ℤ, index < 0 ∨ 1 < index →
        (LaurentPolynomial.T (1 : ℤ) - 1 : LaurentPolynomial ℚ).coeff index = 0 := by
      intro index hindex
      have hzero : index ≠ 0 := by omega
      have hone : (1 : ℤ) ≠ index := by omega
      simp [hone, honeCoeff index hzero]
    simpa only [pow_two, zero_add, Int.reduceAdd] using
      hpolyProduct _ _ 0 1 0 1 hbase hbase
  have hshift : ∀ degree index, index < (-3 : ℤ) ∨ -3 < index →
      (PowerSeries.coeff degree
        (PowerSeries.C (LaurentPolynomial.T (-3) : LaurentPolynomial ℚ))).coeff index =
          0 := by
    apply hconstant _ (-3) (-3) ?_
    intro index hindex
    simp [show (-3 : ℤ) ≠ index by omega]
  let numerator : PowerSeries (LaurentPolynomial ℚ) :=
    (PowerSeries.X - 1) ^ 3 * (PowerSeries.X + 1) ^ 3 *
      PowerSeries.C ((LaurentPolynomial.T 1 - 1) ^ 2) *
      (PowerSeries.X * PowerSeries.C (LaurentPolynomial.T 1) - 1) ^ 2 *
      (PowerSeries.X * PowerSeries.C (LaurentPolynomial.T 2) - 1) *
      PowerSeries.C (LaurentPolynomial.T (-3))
  have hnumerator : ∀ degree index, index < (-3 : ℤ) ∨ 3 < index →
      (PowerSeries.coeff degree numerator).coeff index = 0 := by
    have hpure : ((PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)) - 1) ^ 3 *
        (PowerSeries.X + 1) ^ 3 =
        PowerSeries.map LaurentPolynomial.C
          (((PowerSeries.X : PowerSeries ℚ) - 1) ^ 3 * (PowerSeries.X + 1) ^ 3) := by simp
    have hstart := hproduct
      (((PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)) - 1) ^ 3 *
        (PowerSeries.X + 1) ^ 3) _ 0 0 0 2
      (by rw [hpure]; exact hscalar _) hfirst
    have hmiddle := hproduct _ _ 0 2 0 2 hstart
      (by simpa using hpower _ 0 1 (hlinear 1 (by norm_num)) 2)
    have hend := hproduct _ _ 0 4 0 2 hmiddle (hlinear 2 (by norm_num))
    exact hproduct _ _ 0 6 (-3) (-3) hend hshift
  have hsupport (degree : ℕ) (index : ℤ) (hindex : (degree : ℤ) + 3 < |index|) :
      (PowerSeries.coeff degree leftRationalNumerator).coeff index = 0 := by
    simp only [lt_abs] at hindex
    change (PowerSeries.coeff degree (numerator * inverse)).coeff index = 0
    simp only [PowerSeries.coeff_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro pair hpair
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
    apply hpolyProduct _ _ (-3) 3 (-(pair.2 : ℤ)) pair.2 (hnumerator pair.1)
    · intro exponent hexponent
      exact hinverse pair.2 exponent (by simp only [lt_abs]; omega)
    · omega
  have hrational : denominator * leftRationalNumerator = numerator := by
    have hunit : denominator * inverse = 1 := by
      apply PowerSeries.mul_invOfUnit
      simp [denominator]
    change denominator * (numerator * inverse) = numerator
    calc
      _ = numerator * (denominator * inverse) := by ring
      _ = numerator := by rw [hunit, mul_one]
  have hLambertSum :
    (letI : UniformSpace ℚ := ⊥
     letI : DiscreteUniformity ℚ := ⟨rfl⟩
     HasSum (fun index : ℕ => if index = 0 then 0 else
       PowerSeries.C (-(index : ℚ) ^ 2) *
         PowerSeries.mk (fun degree =>
           (PowerSeries.coeff degree leftRationalNumerator).coeff index) *
         PowerSeries.invOfUnit (1 - PowerSeries.X ^ index) 1) leftLambertSum) := by
    let : UniformSpace ℚ := ⊥
    let : DiscreteUniformity ℚ := ⟨rfl⟩
    apply (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℚ).mpr
    intro degree
    have hzero (index : ℕ) (houtside : index ∉ Finset.range (degree + 4)) :
        PowerSeries.coeff degree (if index = 0 then 0 else
          PowerSeries.C (-(index : ℚ) ^ 2) *
            PowerSeries.mk (fun earlier =>
              (PowerSeries.coeff earlier leftRationalNumerator).coeff index) *
            PowerSeries.invOfUnit (1 - PowerSeries.X ^ index) 1) = 0 := by
      have hlarge : degree + 4 ≤ index := by simpa using houtside
      have hnonzero : index ≠ 0 := by omega
      rw [if_neg hnonzero, mul_assoc, PowerSeries.coeff_C_mul]
      simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk]
      rw [Finset.sum_eq_zero]
      · exact mul_zero _
      · intro pair hpair
        have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
        rw [hsupport pair.1 index (by
          rw [abs_of_nonneg (Int.natCast_nonneg index)]
          omega), zero_mul]
    have hequality : PowerSeries.coeff degree leftLambertSum =
        ∑ index ∈ Finset.range (degree + 4), PowerSeries.coeff degree
          (if index = 0 then 0 else
            PowerSeries.C (-(index : ℚ) ^ 2) *
              PowerSeries.mk (fun earlier =>
                (PowerSeries.coeff earlier leftRationalNumerator).coeff index) *
              PowerSeries.invOfUnit (1 - PowerSeries.X ^ index) 1) := by
      simp only [leftLambertSum, PowerSeries.coeff_mk]
      apply Finset.sum_congr rfl
      intro index _
      split_ifs
      · simp
      · rw [mul_assoc, PowerSeries.coeff_C_mul]
    rw [hequality]
    exact hasSum_sum_of_ne_finset_zero hzero
  have hScalarShift : (1 - PowerSeries.X) ^ 4 *
      (PowerSeries.X * leftScalarMoment) = leftLambertSum := by
    have hconstant : PowerSeries.constantCoeff leftLambertSum = 0 := by
      simp only [leftLambertSum, PowerSeries.constantCoeff_mk]
      apply Finset.sum_eq_zero
      intro index _
      split_ifs with hzero
      · rfl
      · have hpositive : (0 : ℤ) < index := by exact_mod_cast Nat.pos_of_ne_zero hzero
        have hnumeratorZero : PowerSeries.constantCoeff leftRationalNumerator =
            (LaurentPolynomial.T (1 : ℤ) - 1) ^ 2 * LaurentPolynomial.T (-3) := by
          simp only [leftRationalNumerator, map_mul, map_pow, map_sub, map_add,
            PowerSeries.constantCoeff_X, map_one, PowerSeries.constantCoeff_C,
            PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]
          ring
        have hterm : (PowerSeries.constantCoeff leftRationalNumerator).coeff index = 0 := by
          rw [hnumeratorZero, pow_two]
          have hbase : ∀ exponent : ℤ, exponent < 0 ∨ 1 < exponent →
              (LaurentPolynomial.T (1 : ℤ) - 1 : LaurentPolynomial ℚ).coeff exponent =
                0 := by
            intro exponent hexponent
            have hne : exponent ≠ 0 := by omega
            have hone : (1 : ℤ) ≠ exponent := by omega
            simp [hone, honeCoeff exponent hne]
          have hsquare := hpolyProduct _ _ 0 1 0 1 hbase hbase
          apply hpolyProduct _ _ 0 2 (-3) (-3) hsquare
          · intro exponent hexponent
            simp [show (-3 : ℤ) ≠ exponent by omega]
          · omega
        simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
          PowerSeries.constantCoeff_mk]
        rw [hterm, zero_mul, mul_zero]
    have hshift := PowerSeries.sub_const_eq_X_mul_shift leftLambertSum
    rw [hconstant, map_zero, sub_zero] at hshift
    have hunit : ((1 - PowerSeries.X) ^ 4 : PowerSeries ℚ) *
        PowerSeries.invOfUnit ((1 - PowerSeries.X) ^ 4) 1 = 1 := by
      apply PowerSeries.mul_invOfUnit
      simp
    unfold leftScalarMoment
    calc
      _ = (((1 - PowerSeries.X) ^ 4 : PowerSeries ℚ) *
          PowerSeries.invOfUnit ((1 - PowerSeries.X) ^ 4) 1) *
          (PowerSeries.X * PowerSeries.mk fun degree =>
            PowerSeries.coeff (degree + 1) leftLambertSum) := by ring
      _ = leftLambertSum := by rw [hunit, one_mul, ← hshift]
  exact ⟨hrational, hsupport, hLambertSum, hScalarShift⟩

end D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftMoment
