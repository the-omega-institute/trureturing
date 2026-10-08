/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207LeftGauge
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207LeftGauge
   mirror-E: none(waiver:formal-left-gauge-moment)
   anchors: [mathlib/module/Mathlib.RingTheory.LaurentSeries]
   utility: none
   digest: Pairing Laurent exponents recovers the scalar moment of the actual left boundary. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftNormalization
import Mathlib.RingTheory.LaurentSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftGauge

open InversionSeq207LeftNormalization
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

noncomputable def leftGauge : PowerSeries (LaurentPolynomial ℚ) :=
  (PowerSeries.X - PowerSeries.C (LaurentPolynomial.T 1)) ^ 2 *
    (1 - PowerSeries.C (LaurentPolynomial.T 1)) ^ 2 *
    (1 - PowerSeries.X * PowerSeries.C (LaurentPolynomial.T 1)) ^ 2 *
    PowerSeries.C (LaurentPolynomial.T (-3)) * leftKernelBoundary

noncomputable def leftShiftedGauge : PowerSeries (LaurentPolynomial ℚ) :=
  PowerSeries.mk fun degree =>
    ∑ exponent ∈ Finset.Icc (-(degree : ℤ) - 3) ((degree : ℤ) + 3),
      if 0 ≤ (degree : ℤ) - 3 - exponent then
        LaurentPolynomial.C
          ((PowerSeries.coeff ((degree : ℤ) - 3 - exponent).toNat leftGauge).coeff
            exponent) * LaurentPolynomial.T exponent
      else 0

theorem left_gauge_moment :
    (∀ degree : ℕ, ∀ exponent : ℤ, (degree : ℤ) + 6 < 2 * |exponent| →
      (PowerSeries.coeff degree leftGauge).coeff exponent = 0) ∧
    PowerSeries.map (LaurentPolynomial.invert.toRingHom) leftGauge = leftGauge ∧
    (letI : UniformSpace ℚ := ⊥
     letI : DiscreteUniformity ℚ := ⟨rfl⟩
     HasSum (fun index : ℕ => PowerSeries.C ((index : ℚ) ^ 2) *
       PowerSeries.mk (fun degree => (PowerSeries.coeff degree leftGauge).coeff index))
       ((1 - PowerSeries.X) ^ 4 *
         PowerSeries.map (LaurentPolynomial.eval₂ (RingHom.id ℚ) 1) leftKernelBoundary)) ∧
    (∀ index : ℤ,
      let column (series : PowerSeries (LaurentPolynomial ℚ)) : LaurentSeries ℚ :=
        (PowerSeries.mk fun degree => (PowerSeries.coeff degree series).coeff index :
          PowerSeries ℚ)
      column leftShiftedGauge = HahnSeries.single (index + 3) 1 * column leftGauge ∧
        column leftGauge = HahnSeries.single (-index - 3) 1 * column leftShiftedGauge) ∧
    (∀ degree : ℕ, ∀ index : ℤ, (degree : ℤ) + 3 < |index| →
      (PowerSeries.coeff degree leftShiftedGauge).coeff index = 0) ∧
    (letI : UniformSpace (LaurentPolynomial ℚ) := ⊥
     letI : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩
     HasSum (fun index : ℤ =>
       PowerSeries.map LaurentPolynomial.C
           (PowerSeries.mk fun degree =>
             (PowerSeries.coeff degree leftShiftedGauge).coeff index) *
         PowerSeries.C (LaurentPolynomial.T index)) leftShiftedGauge) := by
  classical
  let gauge : PowerSeries (LaurentPolynomial ℚ) :=
    (PowerSeries.X - PowerSeries.C (LaurentPolynomial.T 1)) ^ 2 *
      (1 - PowerSeries.C (LaurentPolynomial.T 1)) ^ 2 *
      (1 - PowerSeries.X * PowerSeries.C (LaurentPolynomial.T 1)) ^ 2 *
      PowerSeries.C (LaurentPolynomial.T (-3))
  have hpolySupport (left right : LaurentPolynomial ℚ)
      (lowerLeft upperLeft lowerRight upperRight : ℤ)
      (hleft : ∀ exponent, exponent < lowerLeft ∨ upperLeft < exponent →
        left.coeff exponent = 0)
      (hright : ∀ exponent, exponent < lowerRight ∨ upperRight < exponent →
        right.coeff exponent = 0) :
      ∀ exponent, exponent < lowerLeft + lowerRight ∨ upperLeft + upperRight < exponent →
        (left * right).coeff exponent = 0 := by
    intro exponent houtside
    rw [AddMonoidAlgebra.coeff_mul_apply_left]
    unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro first _
    dsimp only
    by_cases hfirst : first < lowerLeft ∨ upperLeft < first
    · rw [hleft first hfirst, zero_mul]
    · rw [hright (-first + exponent) (by omega), mul_zero]
  have hseriesSupport (left right : PowerSeries (LaurentPolynomial ℚ))
      (lowerLeft upperLeft lowerRight upperRight : ℤ)
      (hleft : ∀ degree exponent, exponent < lowerLeft ∨ upperLeft < exponent →
        (PowerSeries.coeff degree left).coeff exponent = 0)
      (hright : ∀ degree exponent, exponent < lowerRight ∨ upperRight < exponent →
        (PowerSeries.coeff degree right).coeff exponent = 0) :
      ∀ degree exponent,
        exponent < lowerLeft + lowerRight ∨ upperLeft + upperRight < exponent →
        (PowerSeries.coeff degree (left * right)).coeff exponent = 0 := by
    intro degree exponent houtside
    simp only [PowerSeries.coeff_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro pair _
    exact hpolySupport _ _ _ _ _ _ (hleft pair.1) (hright pair.2) exponent houtside
  have hconstant (location : ℤ) (degree : ℕ) (exponent : ℤ) (hne : location ≠ exponent) :
      (PowerSeries.coeff degree (PowerSeries.C (LaurentPolynomial.T location) :
        PowerSeries (LaurentPolynomial ℚ))).coeff exponent = 0 := by
    simp only [PowerSeries.coeff_C]
    split_ifs
    · simp only [LaurentPolynomial.T_apply, if_neg hne]
    · rfl
  have hidentity (exponent : ℤ) (hne : exponent ≠ 0) :
      (1 : LaurentPolynomial ℚ).coeff exponent = 0 := by
    rw [show (1 : LaurentPolynomial ℚ) = LaurentPolynomial.T 0 by simp]
    simp only [LaurentPolynomial.T_apply, if_neg (Ne.symm hne)]
  have hvariable (degree : ℕ) (exponent : ℤ) (hne : exponent ≠ 0) :
      (PowerSeries.coeff degree (PowerSeries.X :
        PowerSeries (LaurentPolynomial ℚ))).coeff exponent = 0 := by
    simp only [PowerSeries.coeff_X]
    split_ifs
    · exact hidentity exponent hne
    · rfl
  have hone (degree : ℕ) (exponent : ℤ) (hne : exponent ≠ 0) :
      (PowerSeries.coeff degree (1 : PowerSeries (LaurentPolynomial ℚ))).coeff exponent =
        0 := by
    change (PowerSeries.coeff degree (PowerSeries.C (1 : LaurentPolynomial ℚ))).coeff
      exponent = 0
    simp only [PowerSeries.coeff_C]
    split_ifs
    · exact hidentity exponent hne
    · rfl
  have hfirstSupport : ∀ degree exponent, exponent < 0 ∨ 1 < exponent →
      (PowerSeries.coeff degree (PowerSeries.X -
        PowerSeries.C (LaurentPolynomial.T 1) : PowerSeries (LaurentPolynomial ℚ))).coeff
          exponent = 0 := by
    intro degree exponent houtside
    simp only [map_sub, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
    rw [hvariable degree exponent (by omega), hconstant 1 degree exponent (by omega)]
    simp only [sub_self]
  have hsecondSupport : ∀ degree exponent, exponent < 0 ∨ 1 < exponent →
      (PowerSeries.coeff degree (1 - PowerSeries.C (LaurentPolynomial.T 1) :
        PowerSeries (LaurentPolynomial ℚ))).coeff exponent = 0 := by
    intro degree exponent houtside
    simp only [map_sub, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
    rw [hone degree exponent (by omega), hconstant 1 degree exponent (by omega)]
    simp only [sub_self]
  have hthirdSupport : ∀ degree exponent, exponent < 0 ∨ 1 < exponent →
      (PowerSeries.coeff degree (1 - PowerSeries.X *
        PowerSeries.C (LaurentPolynomial.T 1) : PowerSeries (LaurentPolynomial ℚ))).coeff
          exponent = 0 := by
    intro degree exponent houtside
    simp only [map_sub, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
    rw [hone degree exponent (by omega)]
    have hshift : (PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)) *
        PowerSeries.C (LaurentPolynomial.T 1) =
        PowerSeries.C (LaurentPolynomial.T 1) * PowerSeries.X := mul_comm _ _
    rw [hshift, PowerSeries.coeff_C_mul]
    simp only [PowerSeries.coeff_X]
    split_ifs
    · simp only [mul_one, LaurentPolynomial.T_apply, if_neg (by omega : (1 : ℤ) ≠ exponent),
        sub_zero]
    · simp
  have hgaugeSupport : ∀ degree exponent, exponent < -3 ∨ 3 < exponent →
      (PowerSeries.coeff degree gauge).coeff exponent = 0 := by
    have hfirstSquare := hseriesSupport _ _ 0 1 0 1 hfirstSupport hfirstSupport
    have hsecondSquare := hseriesSupport _ _ 0 1 0 1 hsecondSupport hsecondSupport
    have hthirdSquare := hseriesSupport _ _ 0 1 0 1 hthirdSupport hthirdSupport
    simp only [← pow_two] at hfirstSquare hsecondSquare hthirdSquare
    have hfirstTwo := hseriesSupport _ _ 0 2 0 2 hfirstSquare hsecondSquare
    have hfirstThree := hseriesSupport _ _ 0 4 0 2 hfirstTwo hthirdSquare
    apply hseriesSupport _ _ 0 6 (-3) (-3) hfirstThree
    intro degree exponent houtside
    exact hconstant (-3) degree exponent (by omega)
  have hsupport : ∀ degree : ℕ, ∀ exponent : ℤ, (degree : ℤ) + 6 < 2 * |exponent| →
      (PowerSeries.coeff degree leftGauge).coeff exponent = 0 := by
    intro degree exponent hlarge
    change (PowerSeries.coeff degree (gauge * leftKernelBoundary)).coeff exponent = 0
    simp only [PowerSeries.coeff_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro pair hpair
    have hdegree := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
    rw [AddMonoidAlgebra.coeff_mul_apply_left]
    unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro first _
    dsimp only
    by_cases hfirst : first < -3 ∨ 3 < first
    · rw [hgaugeSupport pair.1 first hfirst, zero_mul]
    · have htriangle : |exponent| ≤ |first| + |-first + exponent| := by
        simpa using abs_add_le first (-first + exponent)
      have hbound : |first| ≤ 3 := by rw [abs_le]; omega
      rw [left_boundary_normalization.1 pair.2 (-first + exponent) (by omega), mul_zero]
  have hreflection : PowerSeries.map LaurentPolynomial.invert.toRingHom leftGauge =
      leftGauge := by
    let positive : PowerSeries (LaurentPolynomial ℚ) :=
      PowerSeries.C (LaurentPolynomial.T 1)
    let negative : PowerSeries (LaurentPolynomial ℚ) :=
      PowerSeries.C (LaurentPolynomial.T (-1))
    have hcancel : negative * positive = 1 := by
      simp only [negative, positive, ← map_mul, ← LaurentPolynomial.T_add]
      norm_num
    have hfirst : PowerSeries.X - negative = -negative * (1 - PowerSeries.X * positive) :=
      by linear_combination -PowerSeries.X * hcancel
    have hsecond : 1 - negative = -negative * (1 - positive) := by
      linear_combination -hcancel
    have hthird : 1 - PowerSeries.X * negative = -negative * (PowerSeries.X - positive) :=
      by linear_combination -hcancel
    have hnegativeCube : PowerSeries.C (LaurentPolynomial.T (-3)) = negative ^ 3 := by
      simp only [negative, pow_succ, pow_zero, one_mul]
      rw [← map_mul, ← map_mul, ← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add]
      norm_num
    have hpositiveCube : PowerSeries.C (LaurentPolynomial.T 3) = positive ^ 3 := by
      simp only [positive, pow_succ, pow_zero, one_mul]
      rw [← map_mul, ← map_mul, ← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add]
      norm_num
    have hcancelCube : negative ^ 6 * positive ^ 3 = negative ^ 3 := by
      calc
        _ = negative ^ 3 * (negative * positive) ^ 3 := by ring
        _ = negative ^ 3 := by rw [hcancel]; simp
    have hmapConstant (exponent : ℤ) :
        PowerSeries.map (LaurentPolynomial.invert (R := ℚ)).toRingHom
          (PowerSeries.C (LaurentPolynomial.T exponent)) =
            (PowerSeries.C (LaurentPolynomial.T (-exponent)) :
              PowerSeries (LaurentPolynomial ℚ)) := by
      rw [PowerSeries.map_C]
      exact congrArg PowerSeries.C (LaurentPolynomial.invert_T exponent)
    simp only [leftGauge, map_mul, map_pow, map_sub, map_one, PowerSeries.map_X,
      hmapConstant, left_boundary_normalization.2.2.2]
    change (PowerSeries.X - negative) ^ 2 * (1 - negative) ^ 2 *
      (1 - PowerSeries.X * negative) ^ 2 *
      PowerSeries.C (LaurentPolynomial.T 3) * leftKernelBoundary =
        (PowerSeries.X - positive) ^ 2 * (1 - positive) ^ 2 *
        (1 - PowerSeries.X * positive) ^ 2 *
        PowerSeries.C (LaurentPolynomial.T (-3)) * leftKernelBoundary
    rw [hfirst, hsecond, hthird, hnegativeCube, hpositiveCube]
    calc
      _ = (PowerSeries.X - positive) ^ 2 * (1 - positive) ^ 2 *
          (1 - PowerSeries.X * positive) ^ 2 *
          (negative ^ 6 * positive ^ 3) * leftKernelBoundary := by ring
      _ = _ := by rw [hcancelCube]
  let jet (order : ℕ) : LaurentPolynomial ℚ →ₗ[ℚ] ℚ :=
    (Finsupp.linearCombination ℚ fun exponent : ℤ => (exponent : ℚ) ^ order).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap
  have hmonomial (order : ℕ) (exponent : ℤ) :
      jet order (LaurentPolynomial.T exponent) = (exponent : ℚ) ^ order := by
    simp only [jet, LinearMap.comp_apply, LinearEquiv.coe_coe,
      AddMonoidAlgebra.coeffLinearEquiv_apply, LaurentPolynomial.T,
      AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_single, one_smul]
  have hproduct (left right : LaurentPolynomial ℚ) :
      jet 0 (left * right) = jet 0 left * jet 0 right ∧
      jet 1 (left * right) = jet 1 left * jet 0 right + jet 0 left * jet 1 right ∧
      jet 2 (left * right) = jet 2 left * jet 0 right +
        2 * jet 1 left * jet 1 right + jet 0 left * jet 2 right := by
    induction left using AddMonoidAlgebra.induction_on with
    | of first =>
      have hfirst : (AddMonoidAlgebra.of ℚ ℤ) (Multiplicative.ofAdd first) =
          LaurentPolynomial.T first := rfl
      rw [hfirst]
      induction right using AddMonoidAlgebra.induction_on with
      | of second =>
        have hsecond : (AddMonoidAlgebra.of ℚ ℤ) (Multiplicative.ofAdd second) =
            LaurentPolynomial.T second := rfl
        rw [hsecond]
        rw [← LaurentPolynomial.T_add]
        simp only [hmonomial, Int.cast_add, pow_zero, pow_one]
        constructor
        · ring
        constructor <;> ring
      | add left right hleft hright =>
        simp only [mul_add, map_add]
        rcases hleft with ⟨hleftZero, hleftOne, hleftTwo⟩
        rcases hright with ⟨hrightZero, hrightOne, hrightTwo⟩
        rw [hleftZero, hleftOne, hleftTwo, hrightZero, hrightOne, hrightTwo]
        constructor
        · ring
        constructor <;> ring
      | smul scalar right hright =>
        simp only [mul_smul_comm, map_smul, smul_eq_mul]
        rcases hright with ⟨hzero, hone, htwo⟩
        rw [hzero, hone, htwo]
        constructor
        · ring
        constructor <;> ring
    | add left right hleft hright =>
      simp only [add_mul, map_add]
      rcases hleft with ⟨hleftZero, hleftOne, hleftTwo⟩
      rcases hright with ⟨hrightZero, hrightOne, hrightTwo⟩
      rw [hleftZero, hleftOne, hleftTwo, hrightZero, hrightOne, hrightTwo]
      constructor
      · ring
      constructor <;> ring
    | smul scalar left hleft =>
      simp only [smul_mul_assoc, map_smul, smul_eq_mul]
      rcases hleft with ⟨hzero, hone, htwo⟩
      rw [hzero, hone, htwo]
      constructor
      · ring
      constructor <;> ring
  let moment (order : ℕ) (series : PowerSeries (LaurentPolynomial ℚ)) : PowerSeries ℚ :=
    PowerSeries.mk fun degree => jet order (PowerSeries.coeff degree series)
  have hmomentProduct (left right : PowerSeries (LaurentPolynomial ℚ)) :
      moment 0 (left * right) = moment 0 left * moment 0 right ∧
      moment 1 (left * right) = moment 1 left * moment 0 right +
        moment 0 left * moment 1 right ∧
      moment 2 (left * right) = moment 2 left * moment 0 right +
        2 * moment 1 left * moment 1 right + moment 0 left * moment 2 right := by
    have hexpand (order degree : ℕ) :
        PowerSeries.coeff degree (moment order (left * right)) =
        ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal degree,
          jet order (PowerSeries.coeff pair.1 left * PowerSeries.coeff pair.2 right) := by
      simp only [moment, PowerSeries.coeff_mk, PowerSeries.coeff_mul, map_sum]
    constructor
    · ext degree
      rw [hexpand]
      simp only [PowerSeries.coeff_mul, moment, PowerSeries.coeff_mk]
      apply Finset.sum_congr rfl
      intro pair _
      exact (hproduct _ _).1
    constructor
    · ext degree
      rw [hexpand]
      simp only [map_add, PowerSeries.coeff_mul, moment, PowerSeries.coeff_mk,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro pair _
      exact (hproduct _ _).2.1
    · ext degree
      rw [hexpand]
      have htwice (series : PowerSeries ℚ) :
          PowerSeries.coeff degree (2 * series) = 2 * PowerSeries.coeff degree series := by
        change PowerSeries.coeff degree (PowerSeries.C 2 * series) = _
        rw [PowerSeries.coeff_C_mul]
      rw [show 2 * moment 1 left * moment 1 right =
        2 * (moment 1 left * moment 1 right) by ring]
      simp only [map_add, htwice, PowerSeries.coeff_mul, moment, PowerSeries.coeff_mk]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro pair _
      rw [(hproduct _ _).2.2]
      ring
  have hmomentSub (order : ℕ) (left right : PowerSeries (LaurentPolynomial ℚ)) :
      moment order (left - right) = moment order left - moment order right := by
    ext degree
    simp [moment]
  have hmomentC (order : ℕ) (value : LaurentPolynomial ℚ) :
      moment order (PowerSeries.C value) = PowerSeries.C (jet order value) := by
    ext degree
    cases degree <;> simp [moment, PowerSeries.coeff_C]
  have hmomentX (order : ℕ) : moment order PowerSeries.X =
      if order = 0 then PowerSeries.X else 0 := by
    have hone : (1 : LaurentPolynomial ℚ) = LaurentPolynomial.T 0 := by simp
    by_cases horder : order = 0
    · subst order
      ext degree
      simp only [moment, PowerSeries.coeff_mk, PowerSeries.coeff_X]
      split_ifs with hdegree
      · rw [hone, hmonomial]
        simp [hdegree]
      · rw [map_zero]
        simp only [PowerSeries.coeff_X, if_neg hdegree]
    · ext degree
      simp only [moment, PowerSeries.coeff_mk, PowerSeries.coeff_X, if_neg horder, map_zero]
      split_ifs
      · rw [hone, hmonomial, Int.cast_zero, zero_pow horder]
      · rw [map_zero]
  have hmomentOne (order : ℕ) : moment order 1 = if order = 0 then 1 else 0 := by
    have hone : (1 : LaurentPolynomial ℚ) = LaurentPolynomial.T 0 := by simp
    change moment order (PowerSeries.C 1) = _
    rw [hmomentC, hone, hmonomial]
    split_ifs with horder
    · subst order
      norm_num
    · simp only [Int.cast_zero, zero_pow horder, map_zero]
  let first : PowerSeries (LaurentPolynomial ℚ) :=
    PowerSeries.X - PowerSeries.C (LaurentPolynomial.T 1)
  let second : PowerSeries (LaurentPolynomial ℚ) :=
    1 - PowerSeries.C (LaurentPolynomial.T 1)
  let third : PowerSeries (LaurentPolynomial ℚ) :=
    1 - PowerSeries.X * PowerSeries.C (LaurentPolynomial.T 1)
  let last : PowerSeries (LaurentPolynomial ℚ) := PowerSeries.C (LaurentPolynomial.T (-3))
  have hfirst : moment 0 first = PowerSeries.X - 1 := by
    simp [first, hmomentSub, hmomentX, hmomentC, hmonomial]
  have hsecond : moment 0 second = 0 ∧ moment 1 second = -1 := by
    simp [second, hmomentSub, hmomentOne, hmomentC, hmonomial]
  have hthird : moment 0 third = 1 - PowerSeries.X := by
    change moment 0 (1 - PowerSeries.X * PowerSeries.C (LaurentPolynomial.T 1)) = _
    rw [hmomentSub, hmomentOne, (hmomentProduct _ _).1]
    simp [hmomentX, hmomentC, hmonomial]
  have hlast : moment 0 last = 1 := by
    simp [last, hmomentC, hmonomial]
  have hsecondSquare : moment 0 (second ^ 2) = 0 ∧ moment 1 (second ^ 2) = 0 ∧
      moment 2 (second ^ 2) = 2 := by
    rw [pow_two]
    rcases hmomentProduct second second with ⟨hzero, hone, htwo⟩
    simp_all
  have hfirstSecond : moment 0 (first ^ 2 * second ^ 2) = 0 ∧
      moment 1 (first ^ 2 * second ^ 2) = 0 ∧
      moment 2 (first ^ 2 * second ^ 2) = 2 * (PowerSeries.X - 1) ^ 2 := by
    rcases hmomentProduct (first ^ 2) (second ^ 2) with ⟨hzero, hone, htwo⟩
    have hfirstSquare := (hmomentProduct first first).1
    rw [← pow_two, hfirst] at hfirstSquare
    simp_all
    ring
  have hfirstSecondThird : moment 0 (first ^ 2 * second ^ 2 * third ^ 2) = 0 ∧
      moment 1 (first ^ 2 * second ^ 2 * third ^ 2) = 0 ∧
      moment 2 (first ^ 2 * second ^ 2 * third ^ 2) =
        2 * (1 - PowerSeries.X) ^ 4 := by
    rcases hmomentProduct (first ^ 2 * second ^ 2) (third ^ 2) with ⟨hzero, hone, htwo⟩
    have hthirdSquare := (hmomentProduct third third).1
    rw [← pow_two, hthird] at hthirdSquare
    simp_all
    ring
  have hgauge : moment 0 (first ^ 2 * second ^ 2 * third ^ 2 * last) = 0 ∧
      moment 1 (first ^ 2 * second ^ 2 * third ^ 2 * last) = 0 ∧
      moment 2 (first ^ 2 * second ^ 2 * third ^ 2 * last) =
        2 * (1 - PowerSeries.X) ^ 4 := by
    rcases hmomentProduct (first ^ 2 * second ^ 2 * third ^ 2) last with
      ⟨hzero, hone, htwo⟩
    simp_all
  have heval (polynomial : LaurentPolynomial ℚ) :
      jet 0 polynomial = LaurentPolynomial.eval₂ (RingHom.id ℚ) 1 polynomial := by
    induction polynomial using AddMonoidAlgebra.induction_on with
    | of exponent =>
      have hexponent : (AddMonoidAlgebra.of ℚ ℤ) (Multiplicative.ofAdd exponent) =
          LaurentPolynomial.T exponent := rfl
      rw [hexponent]
      simp [hmonomial, LaurentPolynomial.eval₂_T]
    | add left right hleft hright => simp_all
    | smul scalar polynomial hpolynomial =>
      rw [map_smul, Algebra.smul_def, Algebra.smul_def, map_mul, hpolynomial]
      have hscalar : (algebraMap ℚ (LaurentPolynomial ℚ)) scalar =
          LaurentPolynomial.C scalar := rfl
      rw [hscalar, LaurentPolynomial.eval₂_C]
      rfl
  have hroot : moment 0 leftKernelBoundary =
      PowerSeries.map (LaurentPolynomial.eval₂ (RingHom.id ℚ) 1) leftKernelBoundary := by
    ext degree
    simp [moment, heval]
  have hfinal := (hmomentProduct (first ^ 2 * second ^ 2 * third ^ 2 * last)
    leftKernelBoundary).2.2
  rw [hgauge.1, hgauge.2.1, hgauge.2.2, hroot] at hfinal
  have hfull : PowerSeries.mk (fun degree =>
      (PowerSeries.coeff degree leftGauge).coeff.sum fun exponent weight =>
        (exponent : ℚ) ^ 2 * weight) =
      2 * ((1 - PowerSeries.X) ^ 4 *
        PowerSeries.map (LaurentPolynomial.eval₂ (RingHom.id ℚ) 1) leftKernelBoundary) := by
    simpa [first, second, third, last, leftGauge, moment, jet,
      Finsupp.linearCombination_apply, mul_comm, mul_assoc] using hfinal
  have hshiftCoefficient (degree : ℕ) (index : ℤ) :
      (PowerSeries.coeff degree leftShiftedGauge).coeff index =
        if 0 ≤ (degree : ℤ) - 3 - index then
          (PowerSeries.coeff ((degree : ℤ) - 3 - index).toNat leftGauge).coeff index
        else 0 := by
    simp only [leftShiftedGauge, PowerSeries.coeff_mk, AddMonoidAlgebra.coeff_sum,
      Finsupp.finsetSum_apply]
    by_cases hindex : index ∈ Finset.Icc (-(degree : ℤ) - 3) ((degree : ℤ) + 3)
    · rw [Finset.sum_eq_single index]
      · split_ifs
        · rw [← LaurentPolynomial.single_eq_C_mul_T]
          simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_true]
        · rfl
      · intro other _ hne
        split_ifs
        · rw [← LaurentPolynomial.single_eq_C_mul_T]
          simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hne]
        · rfl
      · exact fun hnot => (hnot hindex).elim
    · rw [Finset.sum_eq_zero]
      · split_ifs with hnonnegative
        · have hcast : (((degree : ℤ) - 3 - index).toNat : ℤ) =
              (degree : ℤ) - 3 - index := Int.toNat_of_nonneg hnonnegative
          rw [hsupport _ index (by
            simp only [Finset.mem_Icc, not_and_or, not_le] at hindex
            rw [hcast]
            rcases hindex with hlow | hhigh
            · rw [abs_of_neg (by omega : index < 0)]
              omega
            · omega)]
        · rfl
      · intro other hother
        have hne : other ≠ index := by
          rintro rfl
          exact hindex hother
        split_ifs
        · rw [← LaurentPolynomial.single_eq_C_mul_T]
          simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hne]
        · rfl
  have hshift (index : ℤ) :
      (PowerSeries.mk (fun degree =>
          (PowerSeries.coeff degree leftShiftedGauge).coeff index) : PowerSeries ℚ) =
        HahnSeries.single (index + 3) (1 : ℚ) *
          (PowerSeries.mk (fun degree =>
            (PowerSeries.coeff degree leftGauge).coeff index) : PowerSeries ℚ) := by
    apply HahnSeries.ext
    funext degree
    rw [HahnSeries.coeff_single_mul, one_mul, PowerSeries.coeff_coe,
      PowerSeries.coeff_coe]
    by_cases hnegative : degree < 0
    · rw [if_pos hnegative]
      split_ifs with hbefore
      · rfl
      · have hnonnegative : 0 ≤ degree - (index + 3) := by omega
        have hcast : ((degree - (index + 3)).natAbs : ℤ) = degree - (index + 3) := by
          rw [Int.natCast_natAbs, abs_of_nonneg hnonnegative]
        rw [PowerSeries.coeff_mk, hsupport _ index (by
          rw [hcast]
          by_cases hsign : 0 ≤ index
          · rw [abs_of_nonneg hsign]
            omega
          · rw [abs_of_neg (by omega : index < 0)]
            omega)]
    · have hnonnegative : 0 ≤ degree := by omega
      rw [if_neg hnegative, PowerSeries.coeff_mk, hshiftCoefficient]
      have hcast : (degree.natAbs : ℤ) = degree := by
        rw [Int.natCast_natAbs, abs_of_nonneg hnonnegative]
      rw [hcast]
      by_cases hbefore : degree - (index + 3) < 0
      · rw [if_pos hbefore, if_neg (by omega)]
      · rw [if_neg hbefore, if_pos (by omega), PowerSeries.coeff_mk]
        have hindex : (degree - 3 - index).toNat = (degree - (index + 3)).natAbs := by
          have hcast : ((degree - (index + 3)).natAbs : ℤ) = degree - (index + 3) := by
            rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
          omega
        rw [hindex]
  have hshiftSupport (degree : ℕ) (index : ℤ) (hlarge : (degree : ℤ) + 3 < |index|) :
      (PowerSeries.coeff degree leftShiftedGauge).coeff index = 0 := by
    rw [hshiftCoefficient]
    split_ifs with hnonnegative
    · have hcast : (((degree : ℤ) - 3 - index).toNat : ℤ) =
          (degree : ℤ) - 3 - index := Int.toNat_of_nonneg hnonnegative
      exact hsupport _ index (by
        rw [hcast]
        by_cases hsign : 0 ≤ index
        · rw [abs_of_nonneg hsign] at hlarge ⊢
          omega
        · rw [abs_of_neg (by omega : index < 0)] at hlarge ⊢
          omega)
    · rfl
  refine ⟨hsupport, hreflection, ?_, ?_, hshiftSupport, ?_⟩
  case refine_2 =>
    intro index
    refine ⟨hshift index, ?_⟩
    dsimp only
    rw [hshift index, ← mul_assoc, HahnSeries.single_mul_single,
      show -index - 3 + (index + 3) = (0 : ℤ) by omega, one_mul,
      ← HahnSeries.C_apply, map_one, one_mul]
  case refine_3 =>
    let : UniformSpace (LaurentPolynomial ℚ) := ⊥
    let : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩
    apply (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff (LaurentPolynomial ℚ)).mpr
    intro degree
    let interval := Finset.Icc (-(degree : ℤ) - 3) ((degree : ℤ) + 3)
    have hfinite : HasSum (fun index : ℤ =>
        LaurentPolynomial.C ((PowerSeries.coeff degree leftShiftedGauge).coeff index) *
          LaurentPolynomial.T index)
        (∑ index ∈ interval,
          LaurentPolynomial.C ((PowerSeries.coeff degree leftShiftedGauge).coeff index) *
            LaurentPolynomial.T index) := by
      apply hasSum_sum_of_ne_finset_zero
      intro index houtside
      rw [hshiftSupport degree index (by
        simp only [interval, Finset.mem_Icc, not_and_or, not_le] at houtside
        rcases houtside with hlow | hhigh
        · rw [abs_of_neg (by omega : index < 0)]
          omega
        · rw [abs_of_pos (by omega : 0 < index)]
          omega), map_zero, zero_mul]
    have hsum : (∑ index ∈ interval,
        LaurentPolynomial.C ((PowerSeries.coeff degree leftShiftedGauge).coeff index) *
          LaurentPolynomial.T index) = PowerSeries.coeff degree leftShiftedGauge := by
      ext exponent
      simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
        ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply]
      by_cases hinside : exponent ∈ interval
      · rw [Finset.sum_eq_single exponent]
        · simp only [ite_true]
        · intro other _ hne
          simp only [if_neg hne]
        · exact fun hnot => (hnot hinside).elim
      · rw [Finset.sum_eq_zero]
        · exact (hshiftSupport degree exponent (by
            simp only [interval, Finset.mem_Icc, not_and_or, not_le] at hinside
            rcases hinside with hlow | hhigh
            · rw [abs_of_neg (by omega : exponent < 0)]
              omega
            · rw [abs_of_pos (by omega : 0 < exponent)]
              omega)).symm
        · intro other hother
          exact if_neg (by rintro rfl; exact hinside hother)
    rw [hsum] at hfinite
    simpa only [PowerSeries.coeff_mul_C, PowerSeries.coeff_map,
      PowerSeries.coeff_mk] using hfinite
  let : UniformSpace ℚ := ⊥
  let : DiscreteUniformity ℚ := ⟨rfl⟩
  apply (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℚ).mpr
  intro degree
  have hsymmetry (exponent : ℤ) :
      (PowerSeries.coeff degree leftGauge).coeff (-exponent) =
        (PowerSeries.coeff degree leftGauge).coeff exponent := by
    have hequality := congrArg (fun series : PowerSeries (LaurentPolynomial ℚ) =>
      (PowerSeries.coeff degree series).coeff exponent) hreflection
    simp only [PowerSeries.coeff_map] at hequality
    change (LaurentPolynomial.invert (PowerSeries.coeff degree leftGauge)).coeff exponent =
      (PowerSeries.coeff degree leftGauge).coeff exponent at hequality
    rw [LaurentPolynomial.invert_apply] at hequality
    exact hequality
  let positive := (Finset.range (degree + 4)).image (fun index : ℕ => (index : ℤ))
  let negative := (Finset.range (degree + 4)).image (fun index : ℕ => -(index : ℤ))
  let weight (exponent : ℤ) : ℚ :=
    (exponent : ℚ) ^ 2 * (PowerSeries.coeff degree leftGauge).coeff exponent
  have hsubset : (PowerSeries.coeff degree leftGauge).coeff.support ⊆ positive ∪ negative :=
    by
    intro exponent hexponent
    have hnonzero := Finsupp.mem_support_iff.mp hexponent
    have hbound : (exponent.natAbs : ℤ) < degree + 4 := by
      rw [Int.natCast_natAbs]
      by_contra hlarge
      exact hnonzero (hsupport degree exponent (by omega))
    have hrange : exponent.natAbs ∈ Finset.range (degree + 4) := by
      simp only [Finset.mem_range]
      exact_mod_cast hbound
    by_cases hnonnegative : 0 ≤ exponent
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨exponent.natAbs, hrange, ?_⟩
      rw [Int.natCast_natAbs, abs_of_nonneg hnonnegative]
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨exponent.natAbs, hrange, ?_⟩
      rw [Int.natCast_natAbs, abs_of_nonpos (by omega), neg_neg]
  have hintersection : ∑ exponent ∈ positive ∩ negative, weight exponent = 0 := by
    apply Finset.sum_eq_zero
    intro exponent hexponent
    rcases Finset.mem_inter.mp hexponent with ⟨hpositive, hnegative⟩
    rcases Finset.mem_image.mp hpositive with ⟨first, _, hfirst⟩
    rcases Finset.mem_image.mp hnegative with ⟨second, _, hsecond⟩
    have hzero : exponent = 0 := by omega
    simp [weight, hzero]
  have hpositive : ∑ exponent ∈ positive, weight exponent =
      ∑ index ∈ Finset.range (degree + 4),
        (index : ℚ) ^ 2 * (PowerSeries.coeff degree leftGauge).coeff index := by
    rw [Finset.sum_image]
    · simp only [weight, Int.cast_natCast]
    · intro first _ second _ hequality
      change (first : ℤ) = (second : ℤ) at hequality
      exact_mod_cast hequality
  have hnegative : ∑ exponent ∈ negative, weight exponent =
      ∑ index ∈ Finset.range (degree + 4),
        (index : ℚ) ^ 2 * (PowerSeries.coeff degree leftGauge).coeff index := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro index _
      simp [weight, hsymmetry]
    · intro first _ second _ hequality
      change -(first : ℤ) = -(second : ℤ) at hequality
      have hcast := neg_injective hequality
      exact_mod_cast hcast
  have hpaired : (PowerSeries.coeff degree leftGauge).coeff.sum
      (fun exponent value => (exponent : ℚ) ^ 2 * value) =
        2 * ∑ index ∈ Finset.range (degree + 4),
          (index : ℚ) ^ 2 * (PowerSeries.coeff degree leftGauge).coeff index := by
    rw [Finsupp.sum_of_support_subset _ hsubset _ (by intros; simp)]
    change (∑ exponent ∈ positive ∪ negative, weight exponent) = _
    have hunion := Finset.sum_union_inter (s₁ := positive) (s₂ := negative) (f := weight)
    rw [hintersection, add_zero, hpositive, hnegative] at hunion
    rw [hunion]
    ring
  have hscalar := congrArg (PowerSeries.coeff degree) hfull
  have htwice (series : PowerSeries ℚ) :
      PowerSeries.coeff degree (2 * series) = 2 * PowerSeries.coeff degree series := by
    change PowerSeries.coeff degree (PowerSeries.C 2 * series) = _
    rw [PowerSeries.coeff_C_mul]
  rw [PowerSeries.coeff_mk, hpaired, htwice] at hscalar
  have hfinite : HasSum (fun index : ℕ =>
      PowerSeries.coeff degree (PowerSeries.C ((index : ℚ) ^ 2) *
        PowerSeries.mk (fun earlier => (PowerSeries.coeff earlier leftGauge).coeff index)))
      (∑ index ∈ Finset.range (degree + 4), PowerSeries.coeff degree
        (PowerSeries.C ((index : ℚ) ^ 2) * PowerSeries.mk
          (fun earlier => (PowerSeries.coeff earlier leftGauge).coeff index))) := by
    apply hasSum_sum_of_ne_finset_zero
    intro index houtside
    have hlarge : degree + 4 ≤ index := by simpa using houtside
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      hsupport degree index (by rw [abs_of_nonneg (Int.natCast_nonneg index)]; omega),
      mul_zero]
  have hequality : (∑ index ∈ Finset.range (degree + 4),
      PowerSeries.coeff degree (PowerSeries.C ((index : ℚ) ^ 2) *
        PowerSeries.mk (fun earlier => (PowerSeries.coeff earlier leftGauge).coeff index))) =
      PowerSeries.coeff degree ((1 - PowerSeries.X) ^ 4 *
        PowerSeries.map (LaurentPolynomial.eval₂ (RingHom.id ℚ) 1) leftKernelBoundary) := by
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    linarith
  rw [hequality] at hfinite
  exact hfinite

end D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftGauge
