/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207KernelCancellation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207KernelCancellation
   mirror-E: none(waiver:formal-rational-kernel-cancellation)
   anchors: []
   utility: none
   digest: One-sided support induction constructs the convergent rational kernel contraction. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftRational

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207KernelCancellation

open InversionSeq207LeftMoment
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

noncomputable def rationalKernel : PowerSeries (LaurentPolynomial ℚ) :=
  (PowerSeries.C (LaurentPolynomial.T (-1) - LaurentPolynomial.T (-2)) +
    PowerSeries.X * PowerSeries.C (LaurentPolynomial.T (-1) - LaurentPolynomial.T 1) +
    PowerSeries.X ^ 2 * PowerSeries.C (LaurentPolynomial.T 2 - LaurentPolynomial.T 1)) *
    PowerSeries.invOfUnit
      (1 + PowerSeries.X * PowerSeries.C (LaurentPolynomial.T (-1) - 2) +
        PowerSeries.X ^ 2 * PowerSeries.C (LaurentPolynomial.T 1 - 2) +
          PowerSeries.X ^ 3) 1

set_option maxHeartbeats 2400000 in
theorem kernel_lambert_cancellation :
    (∀ degree : ℕ, ∀ index : ℤ, (degree : ℤ) < index →
      (PowerSeries.coeff degree rationalKernel).coeff index = 0) ∧
    (letI : UniformSpace ℚ := ⊥
     letI : DiscreteUniformity ℚ := ⟨rfl⟩
     HasSum (fun index : ℕ => if index = 0 then 0 else
       PowerSeries.C (-(index : ℚ) ^ 2) *
         PowerSeries.mk (fun degree =>
           (PowerSeries.coeff degree rationalKernel).coeff index) *
         PowerSeries.invOfUnit (1 - PowerSeries.X ^ index) 1)
       (PowerSeries.X * PowerSeries.invOfUnit (1 - PowerSeries.X) 1 *
         PowerSeries.invOfUnit ((1 + PowerSeries.X) ^ 4) 1 *
         ((1 + PowerSeries.X) ^ 2 + PowerSeries.X * leftScalarMoment))) := by
  classical
  let : UniformSpace ℚ := ⊥
  let : DiscreteUniformity ℚ := ⟨rfl⟩
  let q : PowerSeries ℚ := PowerSeries.X
  let scalar := (PowerSeries.map LaurentPolynomial.C :
    PowerSeries ℚ →+* PowerSeries (LaurentPolynomial ℚ))
  let denominator : PowerSeries (LaurentPolynomial ℚ) :=
    1 + PowerSeries.X * PowerSeries.C (LaurentPolynomial.T (-1) - 2) +
      PowerSeries.X ^ 2 * PowerSeries.C (LaurentPolynomial.T 1 - 2) +
        PowerSeries.X ^ 3
  let inverse := PowerSeries.invOfUnit denominator 1
  let numerator : PowerSeries (LaurentPolynomial ℚ) :=
    PowerSeries.C (LaurentPolynomial.T (-1) - LaurentPolynomial.T (-2)) +
      PowerSeries.X * PowerSeries.C (LaurentPolynomial.T (-1) - LaurentPolynomial.T 1) +
      PowerSeries.X ^ 2 * PowerSeries.C (LaurentPolynomial.T 2 - LaurentPolynomial.T 1)
  let column (series : PowerSeries (LaurentPolynomial ℚ)) (index : ℤ) :=
    PowerSeries.mk fun degree => (PowerSeries.coeff degree series).coeff index
  let term (series : PowerSeries (LaurentPolynomial ℚ)) (index : ℕ) : PowerSeries ℚ :=
    if index = 0 then 0 else
      PowerSeries.C (-(index : ℚ) ^ 2) * column series index *
        PowerSeries.invOfUnit (1 - q ^ index) 1
  let contraction : PowerSeries ℚ := PowerSeries.mk fun degree =>
    ∑ index ∈ Finset.range (degree + 1), PowerSeries.coeff degree (term rationalKernel index)
  have hone (index : ℤ) (hindex : index ≠ 0) :
      (1 : LaurentPolynomial ℚ).coeff index = 0 := by
    change (Finsupp.single 0 (1 : ℚ)) index = 0
    simp [hindex]
  have hproduct (first second : LaurentPolynomial ℚ) (firstBound secondBound : ℤ)
      (hfirst : ∀ index, firstBound < index → first.coeff index = 0)
      (hsecond : ∀ index, secondBound < index → second.coeff index = 0) :
      ∀ index, firstBound + secondBound < index → (first * second).coeff index = 0 := by
    intro index hindex
    rw [AddMonoidAlgebra.coeff_mul_apply_left]
    unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro location _
    dsimp only
    by_cases hlarge : firstBound < location
    · rw [hfirst location hlarge, zero_mul]
    · rw [hsecond (-location + index) (by omega), mul_zero]
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
  have hdenSupport (degree : ℕ) (index : ℤ) (hindex : (degree : ℤ) < index) :
      (PowerSeries.coeff degree denominator).coeff index = 0 := by
    rw [hdenominator]
    by_cases hzero : degree = 0
    · subst degree
      simpa using hone index (by omega)
    by_cases hfirst : degree = 1
    · subst degree
      simp [show index ≠ 0 by omega, show (-1 : ℤ) ≠ index by omega]
    by_cases hsecond : degree = 2
    · subst degree
      simp [show index ≠ 0 by omega, show (1 : ℤ) ≠ index by omega]
    by_cases hthird : degree = 3
    · subst degree
      simpa using hone index (by omega)
    simp [hzero, hfirst, hsecond, hthird]
  have hinverseSupport : ∀ degree : ℕ, ∀ index : ℤ, (degree : ℤ) < index →
      (PowerSeries.coeff degree inverse).coeff index = 0 := by
    intro degree
    induction degree using Nat.strong_induction_on with
    | h degree ih =>
        intro index hindex
        rw [show inverse = PowerSeries.invOfUnit denominator 1 from rfl,
          PowerSeries.coeff_invOfUnit]
        by_cases hzero : degree = 0
        · subst degree
          simpa using hone index (by omega)
        simp only [if_neg hzero, inv_one, Units.val_one, neg_one_mul,
          AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, AddMonoidAlgebra.coeff_sum]
        rw [neg_eq_zero]
        simp only [Finsupp.finsetSum_apply]
        apply Finset.sum_eq_zero
        intro split hsplit
        have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hsplit
        by_cases hless : split.2 < degree
        · simp only [if_pos hless]
          exact hproduct _ _ split.1 split.2 (hdenSupport split.1)
            (ih split.2 hless) index (by omega)
        · simp [hless]
  have hnumSupport (degree : ℕ) (index : ℤ) (hindex : (degree : ℤ) < index) :
      (PowerSeries.coeff degree numerator).coeff index = 0 := by
    have hnum (degree : ℕ) : PowerSeries.coeff degree numerator =
        (if degree = 0 then LaurentPolynomial.T (-1) - LaurentPolynomial.T (-2) else 0) +
          (if degree = 1 then LaurentPolynomial.T (-1) - LaurentPolynomial.T 1 else 0) +
          (if degree = 2 then LaurentPolynomial.T 2 - LaurentPolynomial.T 1 else 0) := by
      simp only [numerator, map_add, PowerSeries.coeff_C]
      congr 1
      · congr 1
        rw [mul_comm, ← pow_one (PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)),
          PowerSeries.coeff_C_mul_X_pow]
      · rw [mul_comm, PowerSeries.coeff_C_mul_X_pow]
    rw [hnum]
    by_cases hzero : degree = 0
    · subst degree
      simp [show (-1 : ℤ) ≠ index by omega, show (-2 : ℤ) ≠ index by omega]
    by_cases hfirst : degree = 1
    · subst degree
      simp [show (-1 : ℤ) ≠ index by omega, show (1 : ℤ) ≠ index by omega]
    by_cases hsecond : degree = 2
    · subst degree
      simp [show (2 : ℤ) ≠ index by omega, show (1 : ℤ) ≠ index by omega]
    simp [hzero, hfirst, hsecond]
  have hkernelSupport (degree : ℕ) (index : ℤ) (hindex : (degree : ℤ) < index) :
      (PowerSeries.coeff degree rationalKernel).coeff index = 0 := by
    change (PowerSeries.coeff degree (numerator * inverse)).coeff index = 0
    rw [PowerSeries.coeff_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro split hsplit
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hsplit
    exact hproduct _ _ split.1 split.2 (hnumSupport split.1)
      (hinverseSupport split.2) index (by omega)
  have htermSupport (degree index : ℕ) (hindex : degree < index) :
      PowerSeries.coeff degree (term rationalKernel index) = 0 := by
    dsimp only [term]
    rw [if_neg (by omega), PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro split hsplit
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hsplit
    rw [PowerSeries.coeff_C_mul]
    have hzero : PowerSeries.coeff split.1 (column rationalKernel index) = 0 := by
      simpa only [column, PowerSeries.coeff_mk] using
        hkernelSupport split.1 index (by omega)
    rw [hzero, mul_zero, zero_mul]
  have hsum : HasSum (term rationalKernel) contraction := by
    apply (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℚ).mpr
    intro degree
    rw [show PowerSeries.coeff degree contraction =
        ∑ index ∈ Finset.range (degree + 1),
          PowerSeries.coeff degree (term rationalKernel index) by
      simp only [contraction, PowerSeries.coeff_mk]]
    apply hasSum_sum_of_ne_finset_zero
    intro index houtside
    exact htermSupport degree index (by simpa using houtside)
  let factor := (1 - q) ^ 5 * (1 + q) ^ 4
  let prefactor := (1 - q) ^ 3 * (1 + q) ^ 3
  let correction : PowerSeries (LaurentPolynomial ℚ) :=
    scalar (q ^ 2) * PowerSeries.C (LaurentPolynomial.T 2) -
      scalar (q * (1 + q)) * PowerSeries.C (LaurentPolynomial.T 1) +
      scalar (1 + q) * PowerSeries.C (LaurentPolynomial.T (-1)) -
        PowerSeries.C (LaurentPolynomial.T (-2))
  have hrational : scalar factor * rationalKernel =
      scalar q * leftRationalNumerator + scalar prefactor * correction := by
    have hdenOne : PowerSeries.constantCoeff denominator = 1 := by
      simp [denominator]
    have hunit : IsUnit denominator :=
      PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hdenOne]; exact isUnit_one)
    apply hunit.mul_left_cancel
    have hcancel : denominator * inverse = 1 :=
      PowerSeries.mul_invOfUnit denominator 1 hdenOne
    have hleft := left_rational_regularity.1
    change denominator * leftRationalNumerator = _ at hleft
    change denominator * (scalar factor * (numerator * inverse)) = _
    rw [show denominator * (scalar factor * (numerator * inverse)) =
        scalar factor * numerator * (denominator * inverse) by ring, hcancel, mul_one]
    conv_rhs =>
      rw [mul_add, show denominator * (scalar q * leftRationalNumerator) =
        scalar q * (denominator * leftRationalNumerator) by ring, hleft]
    dsimp only [scalar, factor, prefactor, correction, denominator, numerator, q]
    simp only [map_mul, map_pow, map_sub, map_add, map_one, PowerSeries.map_X]
    have hnegative : (LaurentPolynomial.T (-2) : LaurentPolynomial ℚ) =
        LaurentPolynomial.T (-1) ^ 2 := by rw [LaurentPolynomial.T_pow]; congr 1
    have hpositive : (LaurentPolynomial.T (2 : ℤ) : LaurentPolynomial ℚ) =
        LaurentPolynomial.T 1 ^ 2 := by rw [LaurentPolynomial.T_pow]; congr 1
    have hthree : (LaurentPolynomial.T (-3) : LaurentPolynomial ℚ) =
        LaurentPolynomial.T (-1) ^ 3 := by rw [LaurentPolynomial.T_pow]; congr 1
    simp only [hnegative, hpositive, hthree, map_pow]
    norm_num only [map_ofNat]
    ring_nf
    simp only [mul_assoc, ← map_pow, ← map_mul, ← LaurentPolynomial.T_add,
      LaurentPolynomial.T_pow]
    norm_num
    ring
  have hcolumnScalar (value : PowerSeries ℚ)
      (series : PowerSeries (LaurentPolynomial ℚ)) (index : ℤ) :
      column (scalar value * series) index = value * column series index := by
    apply PowerSeries.ext
    intro degree
    simp only [column, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
      AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, scalar, PowerSeries.coeff_map]
    apply Finset.sum_congr rfl
    intro split _
    change ((AddMonoidAlgebra.single (0 : ℤ) _ : LaurentPolynomial ℚ) * _).coeff index = _
    simp only [AddMonoidAlgebra.coeff_single_mul_apply, neg_zero, zero_add]
  have hcolumnAdd (first second : PowerSeries (LaurentPolynomial ℚ)) (index : ℤ) :
      column (first + second) index = column first index + column second index := by
    ext degree
    simp [column]
  have hterm (index : ℕ) : factor * term rationalKernel index =
      q * term leftRationalNumerator index + prefactor * term correction index := by
    by_cases hzero : index = 0
    · simp [term, hzero]
    · have hequality := congrArg (fun series => column series index) hrational
      rw [hcolumnAdd, hcolumnScalar, hcolumnScalar, hcolumnScalar] at hequality
      simp only [term, if_neg hzero]
      linear_combination
        (PowerSeries.C (-(index : ℚ) ^ 2) *
          PowerSeries.invOfUnit (1 - q ^ index) 1) * hequality
  have hcorrection (index : ℕ) (hpositive : index ≠ 0) :
      column correction index =
        if index = 1 then -(q * (1 + q)) else if index = 2 then q ^ 2 else 0 := by
    have hmonomial (value : PowerSeries ℚ) (location : ℤ) :
        column (scalar value * PowerSeries.C (LaurentPolynomial.T location)) index =
          if location = (index : ℤ) then value else 0 := by
      ext earlier
      rw [show scalar value * PowerSeries.C (LaurentPolynomial.T location) =
        PowerSeries.C (LaurentPolynomial.T location) * scalar value by ring]
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_map, mul_comm,
        ← LaurentPolynomial.single_eq_C_mul_T]
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      split_ifs <;> simp
    have hcolumnSub (first second : PowerSeries (LaurentPolynomial ℚ)) :
        column (first - second) index = column first index - column second index := by
      ext earlier
      simp [column]
    have hequality : column correction index =
        (if (2 : ℤ) = index then q ^ 2 else 0) -
          (if (1 : ℤ) = index then q * (1 + q) else 0) := by
      dsimp only [correction]
      rw [hcolumnSub, hcolumnAdd, hcolumnSub, hmonomial, hmonomial, hmonomial]
      have hconstant : column (PowerSeries.C (LaurentPolynomial.T (-2))) index = 0 := by
        ext earlier
        have hne : (-2 : ℤ) ≠ index := by omega
        simp only [column, PowerSeries.coeff_mk, PowerSeries.coeff_C]
        split_ifs <;> simp [hne]
      rw [hconstant, if_neg (show (-1 : ℤ) ≠ index by omega), add_zero, sub_zero]
    rw [hequality]
    by_cases hfirst : index = 1
    · simp [hfirst]
    by_cases hsecond : index = 2
    · simp [hsecond]
    simp [hfirst, hsecond, show (1 : ℤ) ≠ index by omega,
      show (2 : ℤ) ≠ index by omega]
  let correctionSum := q * (1 + q) * PowerSeries.invOfUnit (1 - q) 1 -
    4 * q ^ 2 * PowerSeries.invOfUnit (1 - q ^ 2) 1
  have hcorrectionSum : HasSum (term correction) correctionSum := by
    have hfinite : ∀ index ∉ Finset.range 3, term correction index = 0 := by
      intro index houtside
      have hlarge : 3 ≤ index := by simpa using houtside
      simp [term, hcorrection index (by omega), show index ≠ 1 by omega,
        show index ≠ 2 by omega, show index ≠ 0 by omega]
    have hfiniteSum : HasSum (term correction)
        (∑ index ∈ Finset.range 3, term correction index) :=
      hasSum_sum_of_ne_finset_zero hfinite
    convert hfiniteSum using 1
    simp only [Finset.sum_range_succ, term, Nat.cast_ofNat, pow_one]
    rw [hcorrection 1 (by omega)]
    have htwo : column correction (2 : ℤ) = q ^ 2 := by
      simpa using hcorrection 2 (by omega)
    rw [htwo]
    norm_num
    dsimp only [correctionSum]
    norm_num only [map_ofNat]
    ring
  have hwhole : factor * contraction = q * leftLambertSum + prefactor * correctionSum := by
    have hleftSum : HasSum (term leftRationalNumerator) leftLambertSum :=
      left_rational_regularity.2.2.1
    exact (hsum.mul_left factor).unique
      (((hleftSum.mul_left q).add (hcorrectionSum.mul_left prefactor)).congr_fun
        (fun index => hterm index))
  have hminus : (1 - q) * PowerSeries.invOfUnit (1 - q) 1 = 1 :=
    PowerSeries.mul_invOfUnit _ 1 (by simp [q])
  have hplus : (1 + q) ^ 4 * PowerSeries.invOfUnit ((1 + q) ^ 4) 1 = 1 :=
    PowerSeries.mul_invOfUnit _ 1 (by simp [q])
  have hsquare : (1 - q ^ 2) * PowerSeries.invOfUnit (1 - q ^ 2) 1 = 1 :=
    PowerSeries.mul_invOfUnit _ 1 (by simp [q])
  have hregular := left_rational_regularity.2.2.2
  change (1 - q) ^ 4 * (q * leftScalarMoment) = leftLambertSum at hregular
  have hcorrectionCancel : prefactor * correctionSum =
      q * (1 - q) ^ 4 * (1 + q) ^ 2 := by
    dsimp only [prefactor, correctionSum]
    linear_combination
      q * (1 - q) ^ 2 * (1 + q) ^ 4 * hminus -
        4 * q ^ 2 * (1 - q) ^ 2 * (1 + q) ^ 2 * hsquare
  have htarget : factor *
      (q * PowerSeries.invOfUnit (1 - q) 1 *
        PowerSeries.invOfUnit ((1 + q) ^ 4) 1 *
        ((1 + q) ^ 2 + q * leftScalarMoment)) =
      q * leftLambertSum + prefactor * correctionSum := by
    rw [← hregular, hcorrectionCancel]
    dsimp only [factor]
    calc
      _ = q * (1 - q) ^ 4 *
          ((1 - q) * PowerSeries.invOfUnit (1 - q) 1) *
          ((1 + q) ^ 4 * PowerSeries.invOfUnit ((1 + q) ^ 4) 1) *
          ((1 + q) ^ 2 + q * leftScalarMoment) := by ring
      _ = _ := by rw [hminus, hplus]; ring
  have hfactor : factor ≠ 0 := by
    intro hzero
    have hconstant := congrArg PowerSeries.constantCoeff hzero
    simp [factor, q] at hconstant
  have hvalue := mul_left_cancel₀ hfactor (hwhole.trans htarget.symm)
  refine ⟨hkernelSupport, ?_⟩
  simpa only [term, column, q, hvalue] using hsum

end D5.S3.Combinatorics.InversionSeq.InversionSeq207KernelCancellation
