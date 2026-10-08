/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207Lambert
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207Lambert
   mirror-E: none(waiver:formal-theta-lambert-products)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Eigenspace.Basic]
   utility: none
   digest: Finite products and divisor reconstruction compute exact theta Lambert coefficients. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207ThetaDifferential
import D5.S3.Combinatorics.InversionSeq.InversionSeq207Normalization
import D5.S3.Combinatorics.InversionSeq.InversionSeq207Polynomials
import Mathlib.LinearAlgebra.Eigenspace.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207Lambert

open InversionSeq207ThetaSpecialization InversionSeq207ThetaNormalization
open InversionSeq207ThetaDifferential
open InversionSeq207TripleProduct
open Finset.HasAntidiagonal

noncomputable def thetaLambertTail : PowerSeries (LaurentPolynomial ℚ) :=
  let phi := fun input : PowerSeries (LaurentPolynomial ℚ) =>
    input * (1 + input) * PowerSeries.invOfUnit (1 - input) 1 ^ 3
  PowerSeries.mk fun degree => PowerSeries.coeff degree
    (∑ index ∈ Finset.range (degree + 1),
      (phi (PowerSeries.X ^ (index + 1) * PowerSeries.C (LaurentPolynomial.T 1)) -
        phi (PowerSeries.X ^ (index + 1) *
          PowerSeries.C (LaurentPolynomial.T (-1)))))

set_option maxHeartbeats 2400000 in
theorem theta_lambert_identity :
    PowerSeries.map LaurentPolynomial.C (PowerSeries.pentagonalSeries ℚ ^ 6) *
        PowerSeries.C (LaurentPolynomial.T 1) *
        PowerSeries.map (AddMonoidAlgebra.mapDomainRingHom ℚ (AddMonoidHom.mulLeft (2 : ℤ)))
          formalTheta * PowerSeries.C (1 - LaurentPolynomial.T 1) ^ 3 =
      formalTheta ^ 4 *
        (PowerSeries.C (LaurentPolynomial.T 1 * (1 + LaurentPolynomial.T 1)) +
          PowerSeries.C (1 - LaurentPolynomial.T 1) ^ 3 * thetaLambertTail) ∧
    (∀ level index : ℕ,
      (PowerSeries.coeff level thetaLambertTail).coeff (index : ℤ) =
        if 0 < index ∧ index ∣ level ∧ 0 < level then (index : ℚ) ^ 2 else 0) ∧
    (∀ level index : ℕ,
      (PowerSeries.coeff level thetaLambertTail).coeff (-(index : ℤ)) =
        -(PowerSeries.coeff level thetaLambertTail).coeff (index : ℤ)) := by
  classical
  have hcoefficients :
      (∀ level index : ℕ,
        (PowerSeries.coeff level thetaLambertTail).coeff (index : ℤ) =
          if 0 < index ∧ index ∣ level ∧ 0 < level then (index : ℚ) ^ 2 else 0) ∧
      (∀ level index : ℕ,
        (PowerSeries.coeff level thetaLambertTail).coeff (-(index : ℤ)) =
          -(PowerSeries.coeff level thetaLambertTail).coeff (index : ℤ)) := by
    let phi := fun input : PowerSeries (LaurentPolynomial ℚ) =>
      input * (1 + input) * PowerSeries.invOfUnit (1 - input) 1 ^ 3
    let base : PowerSeries ℚ := PowerSeries.X * (1 + PowerSeries.X) *
      (PowerSeries.invOneSubPow ℚ 3).val
    have hbase (index : ℕ) : PowerSeries.coeff index base = (index : ℚ) ^ 2 := by
      dsimp only [base]
      rw [show (PowerSeries.X : PowerSeries ℚ) * (1 + PowerSeries.X) =
        PowerSeries.X + PowerSeries.X ^ 2 by ring, add_mul, map_add]
      cases index with
      | zero => simp
      | succ index =>
          rw [show PowerSeries.coeff (index + 1)
              (PowerSeries.X * (PowerSeries.invOneSubPow ℚ 3).val) =
              PowerSeries.coeff index (PowerSeries.invOneSubPow ℚ 3).val by
            simpa only [pow_one] using
              PowerSeries.coeff_X_pow_mul (PowerSeries.invOneSubPow ℚ 3).val 1 index]
          cases index with
          | zero => norm_num [PowerSeries.invOneSubPow, PowerSeries.coeff_X_pow_mul']
          | succ index =>
              rw [PowerSeries.coeff_X_pow_mul']
              simp only [show 2 ≤ index + 1 + 1 by omega, ite_true,
                show index + 1 + 1 - 2 = index by omega]
              simp only [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
                PowerSeries.coeff_mk, Nat.cast_choose_two, Nat.cast_add, Nat.cast_one]
              ring
    have hphi (spacing : ℕ) (hspacing : 0 < spacing) (location : ℤ) (index : ℕ) :
        PowerSeries.coeff index
            (phi (PowerSeries.X ^ spacing * PowerSeries.C (LaurentPolynomial.T location))) =
          if spacing ∣ index then
            LaurentPolynomial.C (((index / spacing : ℕ) : ℚ) ^ 2) *
              LaurentPolynomial.T ((index / spacing : ℕ) * location)
          else 0 := by
      let transfer := (PowerSeries.expand spacing (by omega) :
          PowerSeries (LaurentPolynomial ℚ) →ₐ[LaurentPolynomial ℚ] _).toRingHom.comp
        ((PowerSeries.rescale (LaurentPolynomial.T location)).comp
          (PowerSeries.map LaurentPolynomial.C))
      let input : PowerSeries (LaurentPolynomial ℚ) :=
        PowerSeries.X ^ spacing * PowerSeries.C (LaurentPolynomial.T location)
      have hinput : transfer PowerSeries.X = input := by
        simp [transfer, PowerSeries.rescale_X, PowerSeries.expand_C, input, mul_comm]
      have hzero : PowerSeries.constantCoeff input = 0 := by simp [input, hspacing.ne']
      have hinverse : transfer (PowerSeries.invOneSubPow ℚ 3).val =
          PowerSeries.invOfUnit (1 - input) 1 ^ 3 := by
        have hunit : IsUnit (1 - input) :=
          PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hzero])
        apply (hunit.pow 3).mul_left_cancel
        have hfirst := congrArg transfer
          (PowerSeries.invOneSubPow ℚ 3).inv_val
        have hsecond := PowerSeries.mul_invOfUnit (1 - input) 1 (by simp [hzero])
        rw [← mul_pow, hsecond, one_pow]
        simpa only [PowerSeries.invOneSubPow_inv_eq_one_sub_pow, map_mul, map_pow,
          map_sub, map_one, hinput] using hfirst
      have htransfer : transfer base = phi input := by
        simp only [base, map_mul, map_add, map_one, hinput, hinverse, phi]
      rw [← htransfer]
      dsimp only [transfer, RingHom.comp_apply]
      change PowerSeries.coeff index
        (PowerSeries.expand spacing (by omega)
          (PowerSeries.rescale (LaurentPolynomial.T location)
            (PowerSeries.map LaurentPolynomial.C base))) = _
      rw [PowerSeries.coeff_expand]
      split_ifs with hdivides
      · rw [PowerSeries.coeff_rescale, PowerSeries.coeff_map, hbase,
          LaurentPolynomial.T_pow, mul_comm]
      · rfl
    have htail (level : ℕ) : PowerSeries.coeff level thetaLambertTail =
        ∑ index ∈ Finset.range (level + 1),
          (PowerSeries.coeff level
              (phi (PowerSeries.X ^ (index + 1) * PowerSeries.C (LaurentPolynomial.T 1))) -
            PowerSeries.coeff level
              (phi (PowerSeries.X ^ (index + 1) * PowerSeries.C (LaurentPolynomial.T (-1))))) := by
      simp only [thetaLambertTail, phi, PowerSeries.coeff_mk, map_sum, map_sub]
    have hterm (level spacing index : ℕ) (hspacing : 0 < spacing) :
        (PowerSeries.coeff level
            (phi (PowerSeries.X ^ spacing * PowerSeries.C (LaurentPolynomial.T 1))) -
          PowerSeries.coeff level
            (phi (PowerSeries.X ^ spacing * PowerSeries.C (LaurentPolynomial.T (-1))))).coeff
              (index : ℤ) =
          if 0 < index ∧ level = spacing * index then (index : ℚ) ^ 2 else 0 := by
      rw [hphi spacing hspacing 1, hphi spacing hspacing (-1)]
      by_cases hdivides : spacing ∣ level
      · simp only [if_pos hdivides, mul_one, mul_neg_one, AddMonoidAlgebra.coeff_sub,
          ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
          Finsupp.sub_apply, Finsupp.single_apply]
        by_cases hindex : index = 0
        · subst index
          simp only [Nat.cast_zero, Nat.lt_irrefl, false_and, ite_false]
          have hzero : -((level / spacing : ℕ) : ℤ) = 0 ↔
              ((level / spacing : ℕ) : ℤ) = 0 := by omega
          simp only [hzero, sub_self]
        · have hpositive : 0 < index := by omega
          have hcount : 0 ≤ ((level / spacing : ℕ) : ℤ) := Int.natCast_nonneg _
          have hnegative : -((level / spacing : ℕ) : ℤ) ≠ index := by omega
          have hmatch : ((level / spacing : ℕ) : ℤ) = index ↔ level = spacing * index := by
            constructor
            · intro hequal
              have hnat : level / spacing = index := by exact_mod_cast hequal
              simpa only [hnat] using (Nat.mul_div_cancel' hdivides).symm
            · intro hequal
              rw [hequal, Nat.mul_div_cancel_left _ hspacing]
          rw [if_neg hnegative, sub_zero]
          simp only [hpositive, true_and, ← hmatch]
          split_ifs with hequal
          · congr 1
            exact_mod_cast hequal
          · rfl
      · simp only [if_neg hdivides, AddMonoidAlgebra.coeff_sub,
          AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, sub_zero]
        rw [if_neg]
        rintro ⟨_, hequal⟩
        exact hdivides (hequal ▸ dvd_mul_right spacing index)
    have hcolumn (level index : ℕ) :
        (PowerSeries.coeff level thetaLambertTail).coeff (index : ℤ) =
          if 0 < index ∧ index ∣ level ∧ 0 < level then (index : ℚ) ^ 2 else 0 := by
      rw [htail]
      simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
      have hterms (other : ℕ) := hterm level (other + 1) index (by omega)
      simp_rw [hterms]
      by_cases hnonzero : 0 < index ∧ index ∣ level ∧ 0 < level
      · obtain ⟨hindex, hdivides, hlevel⟩ := hnonzero
        have hquotient : 0 < level / index := Nat.div_pos (Nat.le_of_dvd hlevel hdivides) hindex
        have hreconstruct : (level / index - 1 + 1) * index = level := by
          rw [Nat.sub_add_cancel hquotient, Nat.div_mul_cancel hdivides]
        have hmember : level / index - 1 ∈ Finset.range (level + 1) := by
          have hbound := Nat.div_le_self level index
          simp only [Finset.mem_range]
          omega
        rw [Finset.sum_eq_single (level / index - 1)]
        · simp [hindex, hreconstruct, hdivides, hlevel]
        · intro other hother hdifferent
          rw [if_neg]
          rintro ⟨_, hequal⟩
          have hquotientEqual : level / index = other + 1 := by
            rw [hequal, Nat.mul_div_cancel _ hindex]
          omega
        · exact fun houtside => (houtside hmember).elim
      · rw [if_neg hnonzero]
        apply Finset.sum_eq_zero
        intro other hother
        rw [if_neg]
        rintro ⟨hindex, hequal⟩
        apply hnonzero
        refine ⟨hindex, ?_, ?_⟩
        · exact hequal ▸ dvd_mul_left index (other + 1)
        · rw [hequal]
          exact Nat.mul_pos (by omega) hindex
    have hreflect (level index : ℕ) :
        (PowerSeries.coeff level thetaLambertTail).coeff (-(index : ℤ)) =
          -(PowerSeries.coeff level thetaLambertTail).coeff (index : ℤ) := by
      have hinvert : LaurentPolynomial.invert (PowerSeries.coeff level thetaLambertTail) =
          -PowerSeries.coeff level thetaLambertTail := by
        rw [htail, map_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro spacing hspacing
        rw [hphi (spacing + 1) (by omega) 1, hphi (spacing + 1) (by omega) (-1)]
        split_ifs
        · simp only [mul_one, mul_neg_one, map_sub, map_mul,
            LaurentPolynomial.invert_C, LaurentPolynomial.invert_T, neg_neg]
          ring
        · simp
      simpa only [LaurentPolynomial.invert_apply, AddMonoidAlgebra.coeff_neg,
        Finsupp.neg_apply] using congrArg (fun poly => poly.coeff (index : ℤ)) hinvert
    exact ⟨hcolumn, hreflect⟩
  refine ⟨?_, hcoefficients.1, hcoefficients.2⟩
  let exponential (value : ℚ) := PowerSeries.rescale value (PowerSeries.exp ℚ)
  let character (value : ℚ) : Multiplicative ℤ →* PowerSeries ℚ :=
    { toFun := fun index => exponential (value * (index.toAdd : ℚ))
      map_one' := by simp [exponential, PowerSeries.rescale_zero]
      map_mul' := by
        intro first second
        change exponential (value * ((first.toAdd + second.toAdd : ℤ) : ℚ)) = _
        rw [PowerSeries.exp_mul_exp_eq_exp_add]
        congr 1
        push_cast
        ring }
  let evaluate (value : ℚ) :=
    AddMonoidAlgebra.liftNCRingHom PowerSeries.C (character value)
      (fun _ _ => Commute.all _ _)
  let evaluation := PowerSeries.map (evaluate 1)
  let evaluatedTail := evaluation thetaLambertTail
  have hevaluate (value : ℚ) (location : ℤ) :
      evaluate value (LaurentPolynomial.T location) = exponential (value * (location : ℚ)) := by
    simp only [evaluate, LaurentPolynomial.T, AddMonoidAlgebra.liftNCRingHom_single,
      map_one, one_mul, character, MonoidHom.coe_mk, OneHom.coe_mk]
    rfl
  have hevaluateC (value scalar : ℚ) :
      evaluate value (LaurentPolynomial.C scalar) = PowerSeries.C scalar := by
    change evaluate value (AddMonoidAlgebra.single 0 scalar) = _
    rw [AddMonoidAlgebra.liftNCRingHom_single]
    change PowerSeries.C scalar * exponential (value * 0) = _
    simp only [mul_zero, exponential, PowerSeries.rescale_zero,
      RingHom.comp_apply, PowerSeries.constantCoeff_exp, map_one, mul_one]
  have hmapInverse (input : PowerSeries (LaurentPolynomial ℚ))
      (hzero : PowerSeries.constantCoeff input = 0) :
      evaluation (PowerSeries.invOfUnit (1 - input) 1) =
        PowerSeries.invOfUnit (1 - evaluation input) 1 := by
    have hconstant : PowerSeries.constantCoeff (1 - evaluation input) = 1 := by
      simp only [map_sub, map_one]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hzero, map_zero, sub_zero]
    have hunit : IsUnit (1 - evaluation input) :=
      PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hconstant]; exact isUnit_one)
    apply hunit.mul_left_cancel
    rw [PowerSeries.mul_invOfUnit _ 1 (by simpa using hconstant)]
    have hequality := congrArg evaluation
      (PowerSeries.mul_invOfUnit (1 - input) 1 (by simp [hzero]))
    simpa only [map_mul, map_sub, map_one] using hequality
  let derivative : Derivation ℚ (PowerSeries (PowerSeries ℚ))
      (PowerSeries (PowerSeries ℚ)) :=
    { toFun := fun series => PowerSeries.mk fun degree =>
        PowerSeries.derivative ℚ (PowerSeries.coeff degree series)
      map_add' := by intros; apply PowerSeries.ext; intro degree; simp
      map_smul' := by intros; apply PowerSeries.ext; intro degree; simp
      map_one_eq_zero' := by
        apply PowerSeries.ext
        intro degree
        change PowerSeries.coeff degree (PowerSeries.mk fun degree =>
          PowerSeries.derivative ℚ (PowerSeries.coeff degree
            (1 : PowerSeries (PowerSeries ℚ)))) = 0
        simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one]
        split_ifs <;> first | exact PowerSeries.derivative_one | exact map_zero _
      leibniz' := by
        intro first second
        apply PowerSeries.ext
        intro degree
        change PowerSeries.coeff degree
            (PowerSeries.mk fun degree =>
              PowerSeries.derivative ℚ (PowerSeries.coeff degree (first * second))) =
          PowerSeries.coeff degree
            (first * (PowerSeries.mk fun degree =>
              PowerSeries.derivative ℚ (PowerSeries.coeff degree second)) +
            second * (PowerSeries.mk fun degree =>
              PowerSeries.derivative ℚ (PowerSeries.coeff degree first)))
        rw [mul_comm second]
        simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul, map_sum,
          Derivation.leibniz, smul_eq_mul, map_add, Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro pair _
        ring }
  let numerator := fun input : PowerSeries (PowerSeries ℚ) =>
    derivative (derivative (derivative input)) * input ^ 2 -
      3 * derivative (derivative input) * derivative input * input +
      2 * derivative input ^ 3
  let phi := fun input : PowerSeries (PowerSeries ℚ) =>
    input * (1 + input) * PowerSeries.invOfUnit (1 - input) 1 ^ 3
  let factorArgument (value : ℚ) (index : ℕ) : PowerSeries (PowerSeries ℚ) :=
    PowerSeries.X ^ (index + 1) * PowerSeries.C (exponential value)
  let finite (cutoff : ℕ) : PowerSeries (PowerSeries ℚ) :=
    ∏ index ∈ Finset.range cutoff,
      ((1 - factorArgument 1 index) * (1 - factorArgument (-1) index))
  let tail (cutoff : ℕ) : PowerSeries (PowerSeries ℚ) :=
    ∑ index ∈ Finset.range cutoff,
      (phi (factorArgument 1 index) - phi (factorArgument (-1) index))
  let initial : PowerSeries (PowerSeries ℚ) := PowerSeries.C (1 - exponential 1)
  let base : PowerSeries (PowerSeries ℚ) := PowerSeries.C (exponential (-(1 / 2))) * initial
  let approximation (cutoff : ℕ) := base * finite cutoff
  have hderivative (input : PowerSeries (PowerSeries ℚ)) (degree : ℕ) :
      PowerSeries.coeff degree (derivative input) =
        PowerSeries.derivative ℚ (PowerSeries.coeff degree input) := by
    change PowerSeries.coeff degree (PowerSeries.mk fun degree =>
      PowerSeries.derivative ℚ (PowerSeries.coeff degree input)) = _
    exact PowerSeries.coeff_mk degree _
  have hformula (input : PowerSeries (PowerSeries ℚ)) : derivative input =
      PowerSeries.mk (fun degree =>
        PowerSeries.derivative ℚ (PowerSeries.coeff degree input)) := by
    apply PowerSeries.ext
    intro degree
    rw [hderivative, PowerSeries.coeff_mk]
  have hmul (first second : PowerSeries (PowerSeries ℚ)) :
      derivative (first * second) = derivative first * second + first * derivative second := by
    rw [derivative.leibniz]
    simp only [smul_eq_mul]
    ring
  have hC (input : PowerSeries ℚ) :
      derivative (PowerSeries.C input) = PowerSeries.C (PowerSeries.derivative ℚ input) := by
    apply PowerSeries.ext
    intro degree
    simp only [hderivative, PowerSeries.coeff_C]
    split_ifs <;> simp
  have hexponential (value : ℚ) :
      PowerSeries.derivative ℚ (exponential value) = PowerSeries.C value * exponential value := by
    ext degree
    simp only [exponential, PowerSeries.coeff_derivative, PowerSeries.coeff_rescale,
      PowerSeries.coeff_C_mul]
    have hcoeff := congrArg (PowerSeries.coeff degree) (PowerSeries.derivative_exp ℚ)
    rw [PowerSeries.coeff_derivative] at hcoeff
    rw [pow_succ]
    linear_combination value ^ (degree + 1) * hcoeff
  have hscaled (value : ℚ) :
      derivative (PowerSeries.C (exponential value)) =
        PowerSeries.C (PowerSeries.C value) * PowerSeries.C (exponential value) := by
    rw [hC, hexponential, map_mul]
  have hconstant (value : ℚ) : derivative (PowerSeries.C (PowerSeries.C value)) = 0 := by
    rw [hC]
    simp
  have hX (index : ℕ) :
      derivative (PowerSeries.X ^ index : PowerSeries (PowerSeries ℚ)) = 0 := by
    ext degree
    simp only [hderivative, PowerSeries.coeff_X_pow]
    split_ifs <;> simp
  have hvariable (value : ℚ) (index : ℕ) : derivative (factorArgument value index) =
      PowerSeries.C (PowerSeries.C value) * factorArgument value index := by
    dsimp only [factorArgument]
    rw [hmul, hX, hscaled]
    ring
  have hproduct (first second : PowerSeries (PowerSeries ℚ)) :
      numerator (first * second) = numerator first * second ^ 3 +
        numerator second * first ^ 3 := by
    dsimp only [numerator]
    simp only [hmul, map_add, map_sub, derivative.map_natCast]
    ring
  have hfactor (value : ℚ) (index : ℕ) (hvalue : value = 1 ∨ value = -1) :
      numerator (1 - factorArgument value index) =
        -PowerSeries.C (PowerSeries.C value) *
          (1 - factorArgument value index) ^ 3 * phi (factorArgument value index) := by
    have hzero : PowerSeries.constantCoeff (factorArgument value index) = 0 := by
      simp [factorArgument]
    have hinverse := PowerSeries.mul_invOfUnit (1 - factorArgument value index) 1
      (by simp [hzero])
    have hcubed := congrArg (fun input : PowerSeries (PowerSeries ℚ) => input ^ 3) hinverse
    rw [mul_pow, one_pow] at hcubed
    dsimp only [numerator, phi]
    simp only [map_sub, derivative.map_one_eq_zero, hvariable, hmul, hconstant,
      map_neg, map_zero, zero_mul, zero_add]
    rcases hvalue with rfl | rfl
    all_goals
      simp only [map_one, map_neg, mul_one, one_mul, neg_mul, mul_neg,
        neg_neg, map_zero, map_neg, derivative.map_one_eq_zero, zero_mul,
        zero_add] at *
    · linear_combination factorArgument 1 index * (1 + factorArgument 1 index) * hcubed
    · linear_combination -factorArgument (-1) index * (1 + factorArgument (-1) index) * hcubed
  have hfinite (cutoff : ℕ) : numerator (finite cutoff) = -(finite cutoff) ^ 3 * tail cutoff := by
    induction cutoff with
    | zero => simp [finite, tail, numerator, derivative.map_one_eq_zero]
    | succ cutoff ih =>
        dsimp only [finite, tail] at *
        rw [Finset.prod_range_succ, Finset.sum_range_succ, hproduct, ih, hproduct,
          hfactor 1 cutoff (Or.inl rfl), hfactor (-1) cutoff (Or.inr rfl)]
        simp only [map_one, map_neg]
        ring
  have hbase : numerator base =
      -PowerSeries.C (exponential (-(1 / 2))) ^ 3 *
        PowerSeries.C (exponential 1 * (1 + exponential 1)) := by
    have hscalar : numerator (PowerSeries.C (exponential (-(1 / 2)))) = 0 := by
      dsimp only [numerator]
      simp only [hscaled, hmul, hconstant, zero_mul, zero_add]
      ring
    have hinitial : numerator initial =
        -PowerSeries.C (exponential 1 * (1 + exponential 1)) := by
      dsimp only [numerator, initial]
      rw [hC]
      simp only [map_sub, PowerSeries.derivative_one, sub_zero, zero_sub,
        hexponential, map_one, one_mul, map_neg, map_mul, hscaled, map_neg,
        hmul, hconstant, map_one, zero_mul, zero_add]
      simp only [map_add, map_one]
      ring
    dsimp only [base]
    rw [hproduct, hscalar, hinitial]
    ring
  have happroximation (cutoff : ℕ) :
      numerator (approximation cutoff) * approximation cutoff * initial ^ 3 =
        -approximation cutoff ^ 4 *
          (PowerSeries.C (exponential 1 * (1 + exponential 1)) + initial ^ 3 * tail cutoff) := by
    dsimp only [approximation]
    rw [hproduct, hbase, hfinite]
    dsimp only [base]
    ring
  have htheta (degree cutoff : ℕ) (hlarge : degree < cutoff) :
      PowerSeries.coeff degree (normalizedTheta (1 : ℚ)) =
        PowerSeries.coeff degree (approximation cutoff) := by
    simpa [approximation, base, finite, factorArgument, initial, exponential] using
      (theta_exponential_normalization (1 : ℚ)).2.2.2 degree cutoff hlarge
  have hphi (degree index : ℕ) (value : ℚ) (hsmall : degree < index + 1) :
      PowerSeries.coeff degree (phi (factorArgument value index)) = 0 := by
    dsimp only [phi, factorArgument]
    rw [show PowerSeries.X ^ (index + 1) * PowerSeries.C (exponential value) *
          (1 + PowerSeries.X ^ (index + 1) * PowerSeries.C (exponential value)) *
          PowerSeries.invOfUnit
            (1 - PowerSeries.X ^ (index + 1) * PowerSeries.C (exponential value)) 1 ^ 3 =
        PowerSeries.X ^ (index + 1) *
          (PowerSeries.C (exponential value) *
            (1 + PowerSeries.X ^ (index + 1) * PowerSeries.C (exponential value)) *
            PowerSeries.invOfUnit
              (1 - PowerSeries.X ^ (index + 1) * PowerSeries.C (exponential value)) 1 ^ 3)
      by ring]
    rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have htailStable (base extra degree : ℕ) (hsmall : degree < base) :
      PowerSeries.coeff degree (tail (base + extra)) = PowerSeries.coeff degree (tail base) := by
    induction extra with
    | zero => simp
    | succ extra ih =>
        rw [show base + (extra + 1) = base + extra + 1 by omega]
        dsimp only [tail]
        rw [Finset.sum_range_succ, map_add, map_sub, hphi degree (base + extra) 1 (by omega),
          hphi degree (base + extra) (-1) (by omega)]
        simpa only [tail, map_sum, map_sub, sub_zero, add_zero] using ih
  have htail (degree cutoff : ℕ) (hlarge : degree < cutoff) :
      PowerSeries.coeff degree evaluatedTail = PowerSeries.coeff degree (tail cutoff) := by
    have hphiMap (location : ℤ) (index : ℕ) :
        evaluation
          (PowerSeries.X ^ (index + 1) * PowerSeries.C (LaurentPolynomial.T location) *
            (1 + PowerSeries.X ^ (index + 1) * PowerSeries.C (LaurentPolynomial.T location)) *
            PowerSeries.invOfUnit
              (1 - PowerSeries.X ^ (index + 1) *
                PowerSeries.C (LaurentPolynomial.T location)) 1 ^ 3) =
        phi (factorArgument (location : ℚ) index) := by
      rw [map_mul, map_mul, map_pow, hmapInverse _ (by simp)]
      simp only [evaluation, map_mul, map_pow, map_add, map_one, PowerSeries.map_X,
        PowerSeries.map_C, hevaluate, one_mul, phi, factorArgument]
    have hdefinition : PowerSeries.coeff degree evaluatedTail =
        PowerSeries.coeff degree (tail (degree + 1)) := by
      change evaluate 1 (PowerSeries.coeff degree thetaLambertTail) = _
      dsimp only [thetaLambertTail]
      rw [PowerSeries.coeff_mk]
      rw [← PowerSeries.coeff_map]
      change PowerSeries.coeff degree (evaluation _) = _
      simp only [map_sum, map_sub, hphiMap, Int.cast_one, Int.cast_neg, tail]
    rw [hdefinition]
    rw [show cutoff = degree + 1 + (cutoff - (degree + 1)) by omega,
      htailStable (degree + 1) (cutoff - (degree + 1)) degree (by omega)]
  have hcongrMul (degree : ℕ) (first second third fourth : PowerSeries (PowerSeries ℚ))
      (hfirst : ∀ earlier ≤ degree, PowerSeries.coeff earlier first =
        PowerSeries.coeff earlier second)
      (hsecond : ∀ earlier ≤ degree, PowerSeries.coeff earlier third =
        PowerSeries.coeff earlier fourth) :
      ∀ earlier ≤ degree, PowerSeries.coeff earlier (first * third) =
        PowerSeries.coeff earlier (second * fourth) := by
    intro earlier hsmall
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro pair hpair
    have hsum := mem_antidiagonal.mp hpair
    rw [hfirst pair.1 (by omega), hsecond pair.2 (by omega)]
  have hcongrPow (degree : ℕ) (first second : PowerSeries (PowerSeries ℚ))
      (hfirst : ∀ earlier ≤ degree, PowerSeries.coeff earlier first =
        PowerSeries.coeff earlier second) (exponent : ℕ) :
      ∀ earlier ≤ degree, PowerSeries.coeff earlier (first ^ exponent) =
        PowerSeries.coeff earlier (second ^ exponent) := by
    induction exponent with
    | zero => simp
    | succ exponent ih => simpa only [pow_succ] using hcongrMul degree _ _ _ _ ih hfirst
  have hcongrDerivative (degree : ℕ) (first second : PowerSeries (PowerSeries ℚ))
      (hfirst : ∀ earlier ≤ degree, PowerSeries.coeff earlier first =
        PowerSeries.coeff earlier second) :
      ∀ earlier ≤ degree, PowerSeries.coeff earlier (derivative first) =
        PowerSeries.coeff earlier (derivative second) := by
    intro earlier hsmall
    rw [hderivative, hderivative, hfirst earlier hsmall]
  have hcongrNumerator (degree : ℕ) (first second : PowerSeries (PowerSeries ℚ))
      (hfirst : ∀ earlier ≤ degree, PowerSeries.coeff earlier first =
        PowerSeries.coeff earlier second) :
      ∀ earlier ≤ degree, PowerSeries.coeff earlier (numerator first) =
        PowerSeries.coeff earlier (numerator second) := by
    have hone := hcongrDerivative degree first second hfirst
    have htwo := hcongrDerivative degree _ _ hone
    have hthree := hcongrDerivative degree _ _ htwo
    have htermFirst := hcongrMul degree _ _ _ _ hthree (hcongrPow degree _ _ hfirst 2)
    have htermSecond := hcongrMul degree _ _ _ _
      (hcongrMul degree _ _ _ _
        (hcongrMul degree (3 : PowerSeries (PowerSeries ℚ)) 3 _ _
          (by intros; rfl) htwo) hone) hfirst
    have htermThird := hcongrMul degree (2 : PowerSeries (PowerSeries ℚ)) 2 _ _
      (by intros; rfl) (hcongrPow degree _ _ hone 3)
    intro earlier hsmall
    dsimp only [numerator]
    rw [map_add, map_sub, map_add, map_sub,
      htermFirst earlier hsmall, htermSecond earlier hsmall, htermThird earlier hsmall]
  have hlimit : numerator (normalizedTheta (1 : ℚ)) * normalizedTheta (1 : ℚ) * initial ^ 3 =
      -normalizedTheta (1 : ℚ) ^ 4 *
        (PowerSeries.C (exponential 1 * (1 + exponential 1)) + initial ^ 3 * evaluatedTail) := by
    apply PowerSeries.ext
    intro degree
    have hfirst : ∀ earlier ≤ degree, PowerSeries.coeff earlier (normalizedTheta (1 : ℚ)) =
        PowerSeries.coeff earlier (approximation (degree + 1)) := by
      intro earlier hsmall
      exact htheta earlier (degree + 1) (by omega)
    have hleft := hcongrMul degree _ _ (initial ^ 3) (initial ^ 3)
      (hcongrMul degree _ _ _ _ (hcongrNumerator degree _ _ hfirst) hfirst) (by intros; rfl)
    have hrightTail := hcongrMul degree (initial ^ 3) (initial ^ 3) _ _ (by intros; rfl)
      (fun earlier hsmall => htail earlier (degree + 1) (by omega))
    have hright := hcongrMul degree _ _
      (PowerSeries.C (exponential 1 * (1 + exponential 1)) + initial ^ 3 * evaluatedTail)
      (PowerSeries.C (exponential 1 * (1 + exponential 1)) + initial ^ 3 * tail (degree + 1))
      (hcongrPow degree _ _ hfirst 4)
      (by intro earlier hsmall; rw [map_add, map_add, hrightTail earlier hsmall])
    simp only [neg_mul]
    rw [hleft degree le_rfl, map_neg, hright degree le_rfl, ← map_neg]
    simpa only [neg_mul] using
      congrArg (PowerSeries.coeff degree) (happroximation (degree + 1))
  have hduplication : numerator (normalizedTheta (1 : ℚ)) * normalizedTheta (1 : ℚ) =
      PowerSeries.map PowerSeries.C ((-PowerSeries.pentagonalSeries ℚ ^ 2) ^ 3) *
        normalizedTheta (2 : ℚ) := by
    convert theta_duplication_derivative using 1
    dsimp only [numerator]
    simp only [hformula]
    ring
  have hsign : PowerSeries.map PowerSeries.C ((-PowerSeries.pentagonalSeries ℚ ^ 2) ^ 3) =
      -PowerSeries.map PowerSeries.C (PowerSeries.pentagonalSeries ℚ ^ 6) := by
    simp only [map_pow, map_neg]
    ring
  rw [hduplication, hsign] at hlimit
  have hequality := neg_inj.mp (by simpa only [neg_mul] using hlimit)
  have hindependent :
      LinearIndependent ℚ (fun location : ℤ => exponential (location : ℚ)) := by
    apply Module.End.eigenvectors_linearIndependent' (PowerSeries.derivative ℚ).toLinearMap
      (fun location : ℤ => (location : ℚ))
      (by intro first second h; change (first : ℚ) = (second : ℚ) at h; exact_mod_cast h)
    intro location
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_genEigenspace_one]
      change PowerSeries.derivative ℚ (exponential (location : ℚ)) =
        (location : ℚ) • exponential (location : ℚ)
      simpa only [Algebra.smul_def, PowerSeries.algebraMap_eq] using hexponential (location : ℚ)
    · intro hzero
      have hconstant := congrArg (PowerSeries.coeff 0) hzero
      norm_num [exponential, PowerSeries.coeff_rescale] at hconstant
  have hlinear (input : LaurentPolynomial ℚ) :
      evaluate 1 input = Finsupp.linearCombination ℚ
        (fun location : ℤ => exponential (location : ℚ)) input.coeff := by
    induction input using LaurentPolynomial.induction_on' with
    | add first second hfirst hsecond =>
        simp only [map_add, AddMonoidAlgebra.coeff_add, hfirst, hsecond]
    | C_mul_T location scalar =>
        rw [← LaurentPolynomial.single_eq_C_mul_T]
        change evaluate 1 (AddMonoidAlgebra.single location scalar) =
          Finsupp.linearCombination ℚ (fun location : ℤ => exponential (location : ℚ))
            (Finsupp.single location scalar)
        rw [AddMonoidAlgebra.liftNCRingHom_single, Finsupp.linearCombination_single]
        change PowerSeries.C scalar * exponential (1 * (location : ℚ)) =
          scalar • exponential (location : ℚ)
        simp only [one_mul, Algebra.smul_def, PowerSeries.algebraMap_eq]
  have hinjective : Function.Injective (evaluate 1) := by
    intro first second hequal
    apply AddMonoidAlgebra.coeff_injective
    apply hindependent.finsuppLinearCombination_injective
    simpa only [← hlinear] using hequal
  let duplicate := AddMonoidAlgebra.mapDomainRingHom ℚ (AddMonoidHom.mulLeft (2 : ℤ))
  have hduplicateSingle (location : ℤ) (scalar : ℚ) :
      duplicate (AddMonoidAlgebra.single location scalar) =
        AddMonoidAlgebra.single (2 * location) scalar :=
    AddMonoidAlgebra.mapDomain_single
  have hdouble : (evaluate 1).comp duplicate = evaluate 2 := by
    apply AddMonoidAlgebra.ringHom_ext'
    · apply RingHom.ext
      intro value
      change evaluate 1 (duplicate (AddMonoidAlgebra.single 0 value)) =
        evaluate 2 (AddMonoidAlgebra.single 0 value)
      rw [hduplicateSingle, mul_zero]
      change evaluate 1 (LaurentPolynomial.C value) = evaluate 2 (LaurentPolynomial.C value)
      rw [hevaluateC, hevaluateC]
    · apply MonoidHom.ext
      intro location
      change evaluate 1 (duplicate (LaurentPolynomial.T location.toAdd)) =
        evaluate 2 (LaurentPolynomial.T location.toAdd)
      change evaluate 1 (duplicate (AddMonoidAlgebra.single location.toAdd 1)) = _
      rw [hduplicateSingle]
      change evaluate 1 (LaurentPolynomial.T (2 * location.toAdd)) = _
      rw [hevaluate, hevaluate]
      simp only [Int.cast_mul, Int.cast_ofNat, one_mul]
  have hnormalized (value : ℚ) : normalizedTheta value =
      PowerSeries.C (exponential (-value * (1 / 2))) *
        PowerSeries.map (evaluate value) formalTheta := by
    rfl
  have hphase (value : ℚ) (index : ℕ) : exponential value ^ index =
      exponential (value * (index : ℚ)) := by
    induction index with
    | zero => simp [exponential, PowerSeries.rescale_zero]
    | succ index ih =>
        rw [pow_succ, ih, PowerSeries.exp_mul_exp_eq_exp_add]
        congr 1
        push_cast
        ring
  have hcancelPhase : PowerSeries.C (exponential 2) *
      PowerSeries.C (exponential (-(1 : ℚ) * (1 / 2))) ^ 4 =
        (1 : PowerSeries (PowerSeries ℚ)) := by
    rw [← map_pow, hphase, ← map_mul, PowerSeries.exp_mul_exp_eq_exp_add]
    norm_num [exponential, PowerSeries.rescale_zero]
  have hshiftPhase : PowerSeries.C (exponential 2) *
      PowerSeries.C (exponential (-(2 : ℚ) * (1 / 2))) =
        (PowerSeries.C (exponential 1) : PowerSeries (PowerSeries ℚ)) := by
    rw [← map_mul, PowerSeries.exp_mul_exp_eq_exp_add]
    norm_num [exponential]
  apply PowerSeries.map_injective (evaluate 1) hinjective
  have hscalar : (evaluate 1).comp LaurentPolynomial.C = PowerSeries.C := by
    apply RingHom.ext
    intro value
    exact hevaluateC 1 value
  have hscalarSeries (series : PowerSeries ℚ) :
      PowerSeries.map (evaluate 1) (PowerSeries.map LaurentPolynomial.C series) =
        PowerSeries.map PowerSeries.C series := by
    change ((PowerSeries.map (evaluate 1)).comp (PowerSeries.map LaurentPolynomial.C))
      series = _
    rw [← PowerSeries.map_comp, hscalar]
  have hdoubleSeries (series : PowerSeries (LaurentPolynomial ℚ)) :
      PowerSeries.map (evaluate 1) (PowerSeries.map duplicate series) =
        PowerSeries.map (evaluate 2) series := by
    change ((PowerSeries.map (evaluate 1)).comp (PowerSeries.map duplicate)) series = _
    rw [← PowerSeries.map_comp, hdouble]
  dsimp only [duplicate] at hdoubleSeries
  simp only [map_mul, map_pow, map_add, PowerSeries.map_C, map_sub, map_one,
    hevaluate, one_mul, Int.cast_one, hscalarSeries, hdoubleSeries]
  rw [← (PowerSeries.map PowerSeries.C).map_pow (PowerSeries.pentagonalSeries ℚ) 6]
  suffices hrawImage :
    PowerSeries.map PowerSeries.C (PowerSeries.pentagonalSeries ℚ ^ 6) *
      PowerSeries.C (exponential 1) * PowerSeries.map (evaluate 2) formalTheta * initial ^ 3 =
    PowerSeries.map (evaluate 1) formalTheta ^ 4 *
      (PowerSeries.C (exponential 1 * (1 + exponential 1)) + initial ^ 3 * evaluatedTail) by
    simpa only [initial, evaluatedTail, evaluation, map_sub, map_one, map_mul, map_add]
      using hrawImage
  have hmultiplied := congrArg (fun input : PowerSeries (PowerSeries ℚ) =>
    PowerSeries.C (exponential 2) * input) hequality
  rw [hnormalized 1, hnormalized 2, mul_pow] at hmultiplied
  calc
    _ = PowerSeries.C (exponential 2) *
        (PowerSeries.map PowerSeries.C (PowerSeries.pentagonalSeries ℚ ^ 6) *
          (PowerSeries.C (exponential (-(2 : ℚ) * (1 / 2))) *
            PowerSeries.map (evaluate 2) formalTheta) * initial ^ 3) := by
          rw [show PowerSeries.C (exponential 2) *
            (PowerSeries.map PowerSeries.C (PowerSeries.pentagonalSeries ℚ ^ 6) *
              (PowerSeries.C (exponential (-(2 : ℚ) * (1 / 2))) *
                PowerSeries.map (evaluate 2) formalTheta) * initial ^ 3) =
            (PowerSeries.C (exponential 2) *
              PowerSeries.C (exponential (-(2 : ℚ) * (1 / 2)))) *
              PowerSeries.map PowerSeries.C (PowerSeries.pentagonalSeries ℚ ^ 6) *
              PowerSeries.map (evaluate 2) formalTheta * initial ^ 3 by ring, hshiftPhase]
          ring
    _ = _ := hmultiplied
    _ = _ := by
      rw [show PowerSeries.C (exponential 2) *
          (PowerSeries.C (exponential (-(1 : ℚ) * (1 / 2))) ^ 4 *
            PowerSeries.map (evaluate 1) formalTheta ^ 4 *
            (PowerSeries.C (exponential 1 * (1 + exponential 1)) + initial ^ 3 * evaluatedTail)) =
          (PowerSeries.C (exponential 2) *
            PowerSeries.C (exponential (-(1 : ℚ) * (1 / 2))) ^ 4) *
            PowerSeries.map (evaluate 1) formalTheta ^ 4 *
            (PowerSeries.C (exponential 1 * (1 + exponential 1)) + initial ^ 3 * evaluatedTail)
        by ring, hcancelPhase, one_mul]

end D5.S3.Combinatorics.InversionSeq.InversionSeq207Lambert
