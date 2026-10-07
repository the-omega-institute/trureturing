/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207TripleProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207TripleProduct
   mirror-E: none(waiver:formal-jacobi-triple-product)
   anchors: []
   utility: none
   digest: Euler convolution and Durfee normalization prove the formal Jacobi triple product. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207Durfee

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207TripleProduct

open InversionSeq207Euler InversionSeq207Durfee
open Finset.HasAntidiagonal
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

noncomputable def shiftedEulerFactor : PowerSeries (LaurentPolynomial ℚ) :=
  PowerSeries.mk fun degree =>
    ∑ index ∈ Finset.range (degree + 2),
      LaurentPolynomial.C
          (PowerSeries.coeff degree (PowerSeries.X ^ index * eulerCoefficients index)) *
        LaurentPolynomial.T (index : ℤ)

noncomputable def formalTheta : PowerSeries (LaurentPolynomial ℚ) :=
  eulerLaurentExpansion *
    PowerSeries.map (LaurentPolynomial.invert.toRingHom) shiftedEulerFactor

set_option maxHeartbeats 3200000 in
theorem formal_triple_product (index : ℤ) :
    PowerSeries.pentagonalSeries ℚ *
        PowerSeries.mk (fun degree => (PowerSeries.coeff degree formalTheta).coeff index) =
      PowerSeries.C ((-1 : ℚ) ^ index.natAbs) *
        PowerSeries.X ^ (if 0 ≤ index then index.toNat.choose 2
          else (index.natAbs + 1).choose 2) := by
  classical
  let q : PowerSeries ℚ := PowerSeries.X
  let column (series : PowerSeries (LaurentPolynomial ℚ)) (location : ℤ) :=
    PowerSeries.mk fun degree => (PowerSeries.coeff degree series).coeff location
  let finiteEuler (bound : ℕ) : LaurentPolynomial (PowerSeries ℚ) :=
    ∑ earlier ∈ Finset.range bound,
      LaurentPolynomial.C (eulerCoefficients earlier) * LaurentPolynomial.T (earlier : ℤ)
  let finiteShifted (bound : ℕ) : LaurentPolynomial (PowerSeries ℚ) :=
    ∑ earlier ∈ Finset.range bound,
      LaurentPolynomial.C (q ^ earlier * eulerCoefficients earlier) *
        LaurentPolynomial.T (earlier : ℤ)
  let finiteTheta (bound : ℕ) :=
    finiteEuler bound * LaurentPolynomial.invert (finiteShifted bound)
  have hchoose (earlier : ℕ) : earlier - 1 ≤ earlier.choose 2 := by
    induction earlier with
    | zero => simp
    | succ earlier ih =>
        rw [show (earlier + 1).choose 2 = earlier + earlier.choose 2 by
          simpa using Nat.choose_succ_succ earlier 1]
        omega
  have hsupport := euler_coefficient_construction.2.2.1
  have hshiftSupport (degree earlier : ℕ) (hsmall : degree < earlier) :
      PowerSeries.coeff degree (q ^ earlier * eulerCoefficients earlier) = 0 := by
    rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have hfiniteColumn (bound : ℕ) (location : ℤ) :
      (finiteTheta bound).coeff location =
        ∑ first ∈ Finset.range bound, ∑ second ∈ Finset.range bound,
          if (first : ℤ) - second = location then
            q ^ second * eulerCoefficients first * eulerCoefficients second else 0 := by
    dsimp only [finiteTheta, finiteEuler, finiteShifted]
    rw [map_sum, Finset.sum_mul]
    simp only [Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    rw [show LaurentPolynomial.invert
        (LaurentPolynomial.C (q ^ second * eulerCoefficients second) *
          LaurentPolynomial.T (second : ℤ)) =
        LaurentPolynomial.C (q ^ second * eulerCoefficients second) *
          LaurentPolynomial.T (-(second : ℤ)) by simp]
    rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.single_mul_single]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, sub_eq_add_neg]
    split_ifs <;> ring
  have hpadding (degree bound : ℕ) (hbound : degree + 2 ≤ bound) :
      PowerSeries.coeff degree eulerLaurentExpansion =
        ∑ earlier ∈ Finset.range bound,
          LaurentPolynomial.C (PowerSeries.coeff degree (eulerCoefficients earlier)) *
            LaurentPolynomial.T (earlier : ℤ) := by
    unfold eulerLaurentExpansion
    rw [PowerSeries.coeff_mk]
    apply Finset.sum_subset (Finset.range_mono hbound)
    intro earlier _ houtside
    have hlarge : degree + 2 ≤ earlier := by simpa using houtside
    rw [hsupport degree earlier (by have := hchoose earlier; omega), map_zero, zero_mul]
  have hshiftPadding (degree bound : ℕ) (hbound : degree + 2 ≤ bound) :
      PowerSeries.coeff degree shiftedEulerFactor =
        ∑ earlier ∈ Finset.range bound,
          LaurentPolynomial.C
              (PowerSeries.coeff degree (q ^ earlier * eulerCoefficients earlier)) *
            LaurentPolynomial.T (earlier : ℤ) := by
    unfold shiftedEulerFactor
    rw [PowerSeries.coeff_mk]
    apply Finset.sum_subset (Finset.range_mono hbound)
    intro earlier _ houtside
    have hlarge : degree + 2 ≤ earlier := by simpa using houtside
    rw [hshiftSupport degree earlier (by omega), map_zero, zero_mul]
  have hfiniteApprox (degree bound : ℕ) (location : ℤ) (hbound : degree + 2 ≤ bound) :
      (PowerSeries.coeff degree formalTheta).coeff location =
        PowerSeries.coeff degree ((finiteTheta bound).coeff location) := by
    rw [formalTheta, PowerSeries.coeff_mul]
    simp only [PowerSeries.coeff_map, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    rw [hfiniteColumn, map_sum]
    simp only [map_sum]
    conv_rhs =>
      arg 2
      ext first
      arg 2
      ext second
      rw [show (if (first : ℤ) - second = location then
          q ^ second * eulerCoefficients first * eulerCoefficients second else 0) =
          if (first : ℤ) - second = location then
            eulerCoefficients first * (q ^ second * eulerCoefficients second) else 0 by
        split_ifs <;> ring]
      rw [apply_ite (PowerSeries.coeff degree), PowerSeries.coeff_mul, map_zero]
    conv_rhs =>
      arg 2
      ext first
      arg 2
      ext second
      rw [show (if (first : ℤ) - second = location then
          ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal degree,
            PowerSeries.coeff pair.1 (eulerCoefficients first) *
              PowerSeries.coeff pair.2 (q ^ second * eulerCoefficients second) else 0) =
          ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal degree,
            if (first : ℤ) - second = location then
              PowerSeries.coeff pair.1 (eulerCoefficients first) *
                PowerSeries.coeff pair.2 (q ^ second * eulerCoefficients second) else 0 by
        split_ifs <;> simp]
    conv_rhs => arg 2; ext first; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro pair hpair
    have hpairSum := mem_antidiagonal.mp hpair
    rw [hpadding pair.1 bound (by omega), hshiftPadding pair.2 bound (by omega)]
    rw [map_sum, Finset.sum_mul]
    simp only [Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    change (LaurentPolynomial.C (PowerSeries.coeff pair.1 (eulerCoefficients first)) *
      LaurentPolynomial.T (first : ℤ) * LaurentPolynomial.invert
        (LaurentPolynomial.C
            (PowerSeries.coeff pair.2 (q ^ second * eulerCoefficients second)) *
          LaurentPolynomial.T (second : ℤ))).coeff location = _
    rw [show LaurentPolynomial.invert (LaurentPolynomial.C
          (PowerSeries.coeff pair.2 (q ^ second * eulerCoefficients second)) *
            LaurentPolynomial.T (second : ℤ)) = LaurentPolynomial.C
          (PowerSeries.coeff pair.2 (q ^ second * eulerCoefficients second)) *
            LaurentPolynomial.T (-(second : ℤ)) by simp]
    rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.single_mul_single]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, sub_eq_add_neg]
  have hcolumnEuler (location : ℤ) :
      column eulerLaurentExpansion location =
        if 0 ≤ location then eulerCoefficients location.toNat else 0 := by
    apply PowerSeries.ext
    intro degree
    dsimp only [column]
    rw [PowerSeries.coeff_mk, eulerLaurentExpansion, PowerSeries.coeff_mk]
    simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply]
    by_cases hnonnegative : 0 ≤ location
    · rw [if_pos hnonnegative]
      by_cases hsmall : location.toNat < degree + 2
      · rw [Finset.sum_eq_single location.toNat]
        · simp [Int.toNat_of_nonneg hnonnegative]
        · intro earlier _ hne
          rw [if_neg (by omega)]
        · simp [hsmall]
      · rw [hsupport degree location.toNat (by
          have := hchoose location.toNat; omega)]
        apply Finset.sum_eq_zero
        intro earlier hearlier
        rw [if_neg (by simp only [Finset.mem_range] at hearlier; omega)]
    · rw [if_neg hnonnegative, map_zero]
      apply Finset.sum_eq_zero
      intro earlier _
      rw [if_neg (by omega)]
  have hcolumnShifted (location : ℤ) :
      column shiftedEulerFactor location =
        if 0 ≤ location then q ^ location.toNat * eulerCoefficients location.toNat else 0 := by
    apply PowerSeries.ext
    intro degree
    dsimp only [column]
    rw [PowerSeries.coeff_mk, shiftedEulerFactor, PowerSeries.coeff_mk]
    simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply]
    by_cases hnonnegative : 0 ≤ location
    · rw [if_pos hnonnegative]
      by_cases hsmall : location.toNat < degree + 2
      · rw [Finset.sum_eq_single location.toNat]
        · simp [Int.toNat_of_nonneg hnonnegative, q]
        · intro earlier _ hne
          rw [if_neg (by omega)]
        · simp [hsmall]
      · rw [hshiftSupport degree location.toNat (by omega)]
        apply Finset.sum_eq_zero
        intro earlier hearlier
        rw [if_neg (by simp only [Finset.mem_range] at hearlier; omega)]
    · rw [if_neg hnonnegative, map_zero]
      apply Finset.sum_eq_zero
      intro earlier _
      rw [if_neg (by omega)]
  have hfactor : eulerLaurentExpansion =
      (1 - PowerSeries.C (LaurentPolynomial.T 1)) * shiftedEulerFactor := by
    apply PowerSeries.ext
    intro degree
    apply LaurentPolynomial.ext
    intro location
    have hrec := congrArg (PowerSeries.coeff location.toNat)
      euler_coefficient_construction.1.2
    have hleft := congrArg (PowerSeries.coeff degree) (hcolumnEuler location)
    have hright := congrArg (PowerSeries.coeff degree) (hcolumnShifted location)
    have hprevious := congrArg (PowerSeries.coeff degree) (hcolumnShifted (location - 1))
    simp only [column, PowerSeries.coeff_mk] at hleft hright hprevious
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_C_mul,
      AddMonoidAlgebra.coeff_sub, Finsupp.coe_sub, Pi.sub_apply]
    change _ = (PowerSeries.coeff degree shiftedEulerFactor).coeff location -
      (AddMonoidAlgebra.single 1 (1 : ℚ) *
        PowerSeries.coeff degree shiftedEulerFactor).coeff location
    rw [AddMonoidAlgebra.coeff_single_mul_apply]
    change _ = _ - (1 : ℚ) * _
    rw [one_mul, hleft, hright]
    have hprevious' : (PowerSeries.coeff degree shiftedEulerFactor).coeff (location - 1) =
        PowerSeries.coeff degree
          (if 0 ≤ location - 1 then
            q ^ (location - 1).toNat * eulerCoefficients (location - 1).toNat else 0) :=
      hprevious
    rw [show -1 + location = location - 1 by omega, hprevious']
    by_cases hnegative : location < 0
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), map_zero]
      ring
    · by_cases hzero : location = 0
      · subst location
        simp [q]
      · have hpositive : 0 < location := by omega
        have hnat : location.toNat = (location - 1).toNat + 1 := by omega
        rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), hnat]
        rw [hnat, sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_rescale, PowerSeries.coeff_rescale] at hrec
        simpa only [q, map_sub, PowerSeries.coeff_mk] using
          congrArg (PowerSeries.coeff degree) hrec
  have hreflection :
      PowerSeries.map (LaurentPolynomial.invert.toRingHom) formalTheta =
        -PowerSeries.C (LaurentPolynomial.T (-1)) * formalTheta := by
    rw [formalTheta, hfactor]
    simp only [map_mul, map_sub, map_one, PowerSeries.map_C]
    rw [show LaurentPolynomial.invert.toRingHom (LaurentPolynomial.T (1 : ℤ)) =
      (LaurentPolynomial.T (-1) : LaurentPolynomial ℚ) from
        LaurentPolynomial.invert_T 1]
    change (1 - PowerSeries.C (LaurentPolynomial.T (-1))) *
      PowerSeries.map (LaurentPolynomial.invert.toRingHom) shiftedEulerFactor *
      PowerSeries.map (LaurentPolynomial.invert.toRingHom)
        (PowerSeries.map (LaurentPolynomial.invert.toRingHom) shiftedEulerFactor) = _
    have hinvolution :
        PowerSeries.map (LaurentPolynomial.invert.toRingHom)
          (PowerSeries.map (LaurentPolynomial.invert.toRingHom) shiftedEulerFactor) =
            shiftedEulerFactor := by
      apply PowerSeries.ext
      intro degree
      simp only [PowerSeries.coeff_map]
      exact LaurentPolynomial.involutive_invert _
    rw [hinvolution]
    have hmonomial : PowerSeries.C (LaurentPolynomial.T (-1) : LaurentPolynomial ℚ) *
        PowerSeries.C (LaurentPolynomial.T 1) = 1 := by
      rw [← map_mul, ← LaurentPolynomial.T_add]
      norm_num
    linear_combination
      -shiftedEulerFactor *
        PowerSeries.map (LaurentPolynomial.invert.toRingHom) shiftedEulerFactor * hmonomial
  have htranspose (earlier : ℕ) :
      column formalTheta (-(earlier : ℤ)) = q ^ earlier * column formalTheta earlier := by
    apply PowerSeries.ext
    intro degree
    dsimp only [column]
    rw [PowerSeries.coeff_mk, hfiniteApprox degree (degree + 2) (-(earlier : ℤ)) (by omega)]
    have hfinite : (finiteTheta (degree + 2)).coeff (-(earlier : ℤ)) =
        q ^ earlier * (finiteTheta (degree + 2)).coeff earlier := by
      rw [hfiniteColumn, hfiniteColumn, Finset.mul_sum]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      by_cases hequal : (first : ℤ) - second = earlier
      · have hsum : first = second + earlier := by omega
        rw [if_pos (by omega), if_pos hequal, hsum, pow_add]
        ring
      · rw [if_neg (by omega), if_neg hequal, mul_zero]
    rw [hfinite, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro pair hpair
    have hpairSum := mem_antidiagonal.mp hpair
    rw [PowerSeries.coeff_mk, hfiniteApprox pair.2 (degree + 2) earlier (by omega)]
  have hrecurrence (earlier : ℕ) :
      column formalTheta (earlier + 1) = -q ^ earlier * column formalTheta earlier := by
    have hreflectionColumn : column formalTheta (-(earlier : ℤ)) =
        -column formalTheta ((earlier : ℤ) + 1) := by
      apply PowerSeries.ext
      intro degree
      have hcoefficient := congrArg (fun series : PowerSeries (LaurentPolynomial ℚ) =>
        (PowerSeries.coeff degree series).coeff (earlier : ℤ)) hreflection
      rw [PowerSeries.coeff_map, neg_mul, map_neg, PowerSeries.coeff_C_mul] at hcoefficient
      change (LaurentPolynomial.invert (PowerSeries.coeff degree formalTheta)).coeff
        (earlier : ℤ) =
          (-(LaurentPolynomial.T (-1) * PowerSeries.coeff degree formalTheta)).coeff
            (earlier : ℤ) at hcoefficient
      rw [LaurentPolynomial.invert_apply] at hcoefficient
      change _ = -(AddMonoidAlgebra.single (-1) (1 : ℚ) *
        PowerSeries.coeff degree formalTheta).coeff (earlier : ℤ) at hcoefficient
      rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul] at hcoefficient
      simpa only [column, PowerSeries.coeff_mk, map_neg, show -(-1) + (earlier : ℤ) =
        (earlier : ℤ) + 1 by omega] using hcoefficient
    rw [htranspose] at hreflectionColumn
    linear_combination hreflectionColumn
  have hconstant : column formalTheta 0 =
      PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1 := by
    let : UniformSpace ℚ := ⊥
    let : DiscreteUniformity ℚ := ⟨rfl⟩
    have hsum := durfee_square_normalization
    apply PowerSeries.ext
    intro degree
    have hfinite : PowerSeries.coeff degree
        (PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1) =
        ∑ earlier ∈ Finset.range (degree + 2),
          PowerSeries.coeff degree (q ^ (earlier ^ 2) *
            (PowerSeries.invOfUnit (eulerDenominator earlier) 1) ^ 2) := by
      have hcoeffSum :=
        ((PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℚ).mp hsum) degree
      have hfiniteSum : HasSum (fun earlier : ℕ =>
          PowerSeries.coeff degree (q ^ (earlier ^ 2) *
            (PowerSeries.invOfUnit (eulerDenominator earlier) 1) ^ 2))
          (∑ earlier ∈ Finset.range (degree + 2),
            PowerSeries.coeff degree (q ^ (earlier ^ 2) *
              (PowerSeries.invOfUnit (eulerDenominator earlier) 1) ^ 2)) := by
        apply hasSum_sum_of_ne_finset_zero
        intro earlier houtside
        have hlarge : degree + 2 ≤ earlier := by simpa using houtside
        rw [PowerSeries.coeff_X_pow_mul', if_neg (by nlinarith)]
      exact hcoeffSum.unique hfiniteSum
    rw [hfinite]
    dsimp only [column]
    rw [PowerSeries.coeff_mk, hfiniteApprox degree (degree + 2) 0 (by omega),
      hfiniteColumn, map_sum]
    apply Finset.sum_congr rfl
    intro earlier hearlier
    have hdiagonal : (∑ second ∈ Finset.range (degree + 2),
        if (earlier : ℤ) - second = 0 then
          q ^ second * eulerCoefficients earlier * eulerCoefficients second else 0) =
        q ^ earlier * eulerCoefficients earlier ^ 2 := by
      rw [Finset.sum_eq_single earlier]
      · simp only [sub_self, if_true]
        ring
      · intro second _ hne
        rw [if_neg (by omega)]
      · exact fun houtside => (houtside hearlier).elim
    rw [hdiagonal]
    apply congrArg (PowerSeries.coeff degree)
    have hexponent (amount : ℕ) : amount + 2 * amount.choose 2 = amount ^ 2 := by
      induction amount with
      | zero => simp
      | succ amount ih =>
          rw [show (amount + 1).choose 2 = amount + amount.choose 2 by
            simpa using Nat.choose_succ_succ amount 1]
          nlinarith
    have hsign : ((-1 : ℚ) ^ earlier) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm earlier 2, pow_mul]
      norm_num
    rw [eulerCoefficients, mul_pow, mul_pow, ← map_pow, hsign, map_one, one_mul,
      ← pow_mul, ← mul_assoc, ← pow_add,
      show earlier + earlier.choose 2 * 2 = earlier ^ 2 by have := hexponent earlier; omega]
  have hnormalizedZero : PowerSeries.pentagonalSeries ℚ * column formalTheta 0 = 1 := by
    rw [hconstant]
    apply PowerSeries.mul_invOfUnit
    simpa only [pentagonal, zero_mul, Int.zero_ediv, Int.toNat_zero, Int.negOnePow_zero,
      Units.val_one, Int.cast_one, PowerSeries.coeff_zero_eq_constantCoeff_apply] using
        PowerSeries.coeff_pentagonalSeries_pentagonal ℚ 0
  have hpositive (earlier : ℕ) :
      PowerSeries.pentagonalSeries ℚ * column formalTheta earlier =
        PowerSeries.C ((-1 : ℚ) ^ earlier) * q ^ earlier.choose 2 := by
    induction earlier with
    | zero => simpa using hnormalizedZero
    | succ earlier ih =>
        rw [show ((earlier + 1 : ℕ) : ℤ) = (earlier : ℤ) + 1 by omega, hrecurrence]
        rw [show PowerSeries.pentagonalSeries ℚ *
            (-q ^ earlier * column formalTheta earlier) =
            -q ^ earlier * (PowerSeries.pentagonalSeries ℚ * column formalTheta earlier) by
          ring, ih]
        simp only [show (earlier + 1).choose 2 = earlier + earlier.choose 2 by
          simpa using Nat.choose_succ_succ earlier 1, pow_add, pow_succ, mul_neg_one,
          map_neg, q]
        ring
  change PowerSeries.pentagonalSeries ℚ * column formalTheta index = _
  by_cases hnonnegative : 0 ≤ index
  · have hindex : index = (index.toNat : ℤ) := by omega
    simpa only [if_pos hnonnegative, show index.natAbs = index.toNat by omega,
      Int.toNat_of_nonneg hnonnegative, q] using hpositive index.toNat
  · have hindex : index = -(index.natAbs : ℤ) := by omega
    rw [if_neg hnonnegative]
    conv_lhs => arg 2; rw [hindex, htranspose]
    rw [show PowerSeries.pentagonalSeries ℚ *
        (q ^ index.natAbs * column formalTheta index.natAbs) =
        q ^ index.natAbs * (PowerSeries.pentagonalSeries ℚ *
          column formalTheta index.natAbs) by ring, hpositive]
    simp only [show (index.natAbs + 1).choose 2 = index.natAbs + index.natAbs.choose 2 by
      simpa using Nat.choose_succ_succ index.natAbs 1, pow_add, q]
    ring

end D5.S3.Combinatorics.InversionSeq.InversionSeq207TripleProduct
