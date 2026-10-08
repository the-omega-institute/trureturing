/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207OddLambert
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207OddLambert
   mirror-E: none(waiver:odd-product-logarithmic-calculation)
   anchors: []
   utility: none
   digest: Finite odd products give the locally finite logarithmic Lambert expansion. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207Lambert

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207OddLambert

open Finset.HasAntidiagonal

noncomputable def oddThetaDenominator : PowerSeries (LaurentPolynomial ℚ) :=
  PowerSeries.mk fun degree => PowerSeries.coeff degree
    (∏ index ∈ Finset.range (degree + 1),
      (1 - PowerSeries.X ^ (2 * index + 1) * PowerSeries.C (LaurentPolynomial.T 1)) *
        (1 - PowerSeries.X ^ (2 * index + 1) *
          PowerSeries.C (LaurentPolynomial.T (-1))))

set_option maxHeartbeats 600000 in
theorem odd_product_logarithmic_expansion :
    let derivative := fun series : PowerSeries (LaurentPolynomial ℚ) =>
      PowerSeries.mk fun degree =>
        (Finsupp.linearCombination ℚ
          (fun location : ℤ => LaurentPolynomial.C (location : ℚ) *
            LaurentPolynomial.T location)) (PowerSeries.coeff degree series).coeff
    let lambert : PowerSeries (LaurentPolynomial ℚ) := PowerSeries.mk fun degree =>
      ∑ index ∈ Finset.range (degree + 1),
        if 0 < index ∧ index ∣ degree ∧ Odd (degree / index) then
          LaurentPolynomial.C ((index : ℚ) ^ 2) *
            (LaurentPolynomial.T (index : ℤ) - LaurentPolynomial.T (-(index : ℤ)))
        else 0
    PowerSeries.constantCoeff oddThetaDenominator = 1 ∧
      derivative (derivative (derivative oddThetaDenominator)) * oddThetaDenominator ^ 2 -
        3 * derivative (derivative oddThetaDenominator) *
          derivative oddThetaDenominator * oddThetaDenominator +
        2 * derivative oddThetaDenominator ^ 3 = -oddThetaDenominator ^ 3 * lambert := by
  classical
  let linear : LaurentPolynomial ℚ →ₗ[ℚ] LaurentPolynomial ℚ :=
    (Finsupp.linearCombination ℚ (fun location : ℤ =>
      LaurentPolynomial.C (location : ℚ) * LaurentPolynomial.T location)).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap
  have hsingle (location : ℤ) (value : ℚ) :
      linear (AddMonoidAlgebra.single location value) =
        AddMonoidAlgebra.single location ((location : ℚ) * value) := by
    change (Finsupp.linearCombination ℚ _)
      (Finsupp.single location value) = _
    rw [Finsupp.linearCombination_single, LaurentPolynomial.smul_eq_C_mul,
      ← mul_assoc, ← map_mul, mul_comm value, ← LaurentPolynomial.single_eq_C_mul_T]
  have hleibniz (first second : LaurentPolynomial ℚ) :
      linear (first * second) = first * linear second + linear first * second := by
    induction first using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add first other hfirst hother =>
        simp only [add_mul, map_add, hfirst, hother, mul_add]
        abel
    | single location value =>
        induction second using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add first other hfirst hother =>
            simp only [mul_add, map_add, hfirst, hother, add_mul]
            abel
        | single other scalar =>
            simp only [AddMonoidAlgebra.single_mul_single, hsingle, Int.cast_add,
              ← AddMonoidAlgebra.single_add]
            congr 1
            ring
  let derivative : Derivation ℚ (PowerSeries (LaurentPolynomial ℚ))
      (PowerSeries (LaurentPolynomial ℚ)) :=
    { toFun := fun series => PowerSeries.mk fun degree => linear (PowerSeries.coeff degree series)
      map_add' := by intros; apply PowerSeries.ext; intro degree; simp
      map_smul' := by intros; apply PowerSeries.ext; intro degree; simp
      map_one_eq_zero' := by
        apply PowerSeries.ext
        intro degree
        change PowerSeries.coeff degree (PowerSeries.mk fun degree =>
          linear (PowerSeries.coeff degree (1 : PowerSeries (LaurentPolynomial ℚ)))) =
            PowerSeries.coeff degree 0
        simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one, map_zero]
        split_ifs
        · simpa only [AddMonoidAlgebra.one_def, Int.cast_zero, zero_mul,
            AddMonoidAlgebra.single_zero] using hsingle 0 1
        · exact linear.map_zero
      leibniz' := by
        intro first second
        apply PowerSeries.ext
        intro degree
        change PowerSeries.coeff degree (PowerSeries.mk fun degree =>
          linear (PowerSeries.coeff degree (first * second))) =
          PowerSeries.coeff degree
            (first * PowerSeries.mk (fun degree => linear (PowerSeries.coeff degree second)) +
              second * PowerSeries.mk (fun degree => linear (PowerSeries.coeff degree first)))
        rw [mul_comm second]
        simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul, map_sum, hleibniz,
          smul_eq_mul, map_add, Finset.sum_add_distrib]
        }
  let argument (location : ℤ) (index : ℕ) : PowerSeries (LaurentPolynomial ℚ) :=
    PowerSeries.X ^ (2 * index + 1) * PowerSeries.C (LaurentPolynomial.T location)
  let finite (cutoff : ℕ) : PowerSeries (LaurentPolynomial ℚ) :=
    ∏ index ∈ Finset.range cutoff, (1 - argument 1 index) * (1 - argument (-1) index)
  let phi (input : PowerSeries (LaurentPolynomial ℚ)) :=
    input * (1 + input) * PowerSeries.invOfUnit (1 - input) 1 ^ 3
  let tail (cutoff : ℕ) :=
    ∑ index ∈ Finset.range cutoff, (phi (argument 1 index) - phi (argument (-1) index))
  let numerator (input : PowerSeries (LaurentPolynomial ℚ)) :=
    derivative (derivative (derivative input)) * input ^ 2 -
      3 * derivative (derivative input) * derivative input * input + 2 * derivative input ^ 3
  have hcoeff (series : PowerSeries (LaurentPolynomial ℚ)) (degree : ℕ) :
      PowerSeries.coeff degree (derivative series) = linear (PowerSeries.coeff degree series) :=
    by
      change PowerSeries.coeff degree (PowerSeries.mk fun degree =>
        linear (PowerSeries.coeff degree series)) = _
      exact PowerSeries.coeff_mk degree _
  have hraw (series : PowerSeries (LaurentPolynomial ℚ)) :
      (PowerSeries.mk fun degree =>
        (Finsupp.linearCombination ℚ (fun location : ℤ =>
          LaurentPolynomial.C (location : ℚ) * LaurentPolynomial.T location))
            (PowerSeries.coeff degree series).coeff) = derivative series := by
    rfl
  have hmul (first second : PowerSeries (LaurentPolynomial ℚ)) :
      derivative (first * second) = derivative first * second + first * derivative second := by
    rw [derivative.leibniz]
    simp only [smul_eq_mul]
    ring
  have hconstant (value : ℚ) : derivative (PowerSeries.C (LaurentPolynomial.C value)) = 0 := by
    apply PowerSeries.ext
    intro degree
    simp only [hcoeff, PowerSeries.coeff_C, map_zero]
    split_ifs
    · change linear (AddMonoidAlgebra.single 0 value) = 0
      rw [hsingle]
      simp
    · exact linear.map_zero
  have hargument (location : ℤ) (index : ℕ) :
      derivative (argument location index) =
        PowerSeries.C (LaurentPolynomial.C (location : ℚ)) * argument location index := by
    apply PowerSeries.ext
    intro degree
    simp only [hcoeff, argument, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C,
      PowerSeries.coeff_C_mul]
    have hT : linear (LaurentPolynomial.T location) =
        LaurentPolynomial.C (location : ℚ) * LaurentPolynomial.T location := by
      change linear (AddMonoidAlgebra.single location 1) =
        LaurentPolynomial.C (location : ℚ) * LaurentPolynomial.T location
      rw [hsingle, mul_one, ← LaurentPolynomial.single_eq_C_mul_T]
    split_ifs <;> simp only [hT, map_zero, mul_zero]
  have hproduct (first second : PowerSeries (LaurentPolynomial ℚ)) :
      numerator (first * second) = numerator first * second ^ 3 +
        numerator second * first ^ 3 := by
    dsimp only [numerator]
    simp only [hmul, map_add, map_sub, derivative.map_natCast]
    ring
  have hfactor (location : ℤ) (index : ℕ) (hlocation : location = 1 ∨ location = -1) :
      numerator (1 - argument location index) =
        -PowerSeries.C (LaurentPolynomial.C (location : ℚ)) *
          (1 - argument location index) ^ 3 * phi (argument location index) := by
    have hzero : PowerSeries.constantCoeff (argument location index) = 0 := by
      simp [argument]
    have hinverse := PowerSeries.mul_invOfUnit (1 - argument location index) 1
      (by simp [hzero])
    have hcubed := congrArg (fun input : PowerSeries (LaurentPolynomial ℚ) => input ^ 3) hinverse
    rw [mul_pow, one_pow] at hcubed
    dsimp only [numerator, phi]
    simp only [map_sub, derivative.map_one_eq_zero, hargument, hmul, hconstant,
      map_neg, map_zero, zero_mul, zero_add]
    rcases hlocation with rfl | rfl
    all_goals
      simp only [Int.cast_one, Int.cast_neg, map_one, map_neg, mul_one, one_mul,
        neg_mul, mul_neg, neg_neg, map_zero, map_neg, derivative.map_one_eq_zero,
        zero_mul, zero_add] at *
    · linear_combination argument 1 index * (1 + argument 1 index) * hcubed
    · linear_combination -argument (-1) index * (1 + argument (-1) index) * hcubed
  have hfinite (cutoff : ℕ) : numerator (finite cutoff) = -(finite cutoff) ^ 3 * tail cutoff := by
    induction cutoff with
    | zero => simp [finite, tail, numerator, derivative.map_one_eq_zero]
    | succ cutoff ih =>
        dsimp only [finite, tail] at *
        rw [Finset.prod_range_succ, Finset.sum_range_succ, hproduct, ih, hproduct,
          hfactor 1 cutoff (Or.inl rfl), hfactor (-1) cutoff (Or.inr rfl)]
        simp only [Int.cast_one, Int.cast_neg, map_one, map_neg]
        ring
  have hstable (base extra degree : ℕ) (hlarge : degree < base) :
      PowerSeries.coeff degree (finite (base + extra)) =
        PowerSeries.coeff degree (finite base) := by
    induction extra generalizing degree with
    | zero => simp
    | succ extra ih =>
        rw [show base + (extra + 1) = base + extra + 1 by omega]
        dsimp only [finite]
        rw [Finset.prod_range_succ]
        have hvanish (series : PowerSeries (LaurentPolynomial ℚ)) (location : ℤ) :
            PowerSeries.coeff degree (series * argument location (base + extra)) = 0 := by
          rw [show series * argument location (base + extra) =
            PowerSeries.X ^ (2 * (base + extra) + 1) *
              (series * PowerSeries.C (LaurentPolynomial.T location)) by simp [argument]; ring]
          rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
        rw [show (∏ index ∈ Finset.range (base + extra),
            (1 - argument 1 index) * (1 - argument (-1) index)) *
            ((1 - argument 1 (base + extra)) * (1 - argument (-1) (base + extra))) =
            finite (base + extra) - finite (base + extra) * argument 1 (base + extra) -
              finite (base + extra) * argument (-1) (base + extra) +
              (finite (base + extra) * argument 1 (base + extra)) *
                argument (-1) (base + extra) by dsimp only [finite]; ring]
        rw [map_add, map_sub, map_sub, hvanish, hvanish, hvanish,
          sub_zero, sub_zero, add_zero]
        exact ih degree hlarge
  have happroximation (degree cutoff : ℕ) (hlarge : degree < cutoff) :
      PowerSeries.coeff degree oddThetaDenominator = PowerSeries.coeff degree (finite cutoff) := by
    have hequality := hstable (degree + 1) (cutoff - (degree + 1)) degree (by omega)
    rw [show degree + 1 + (cutoff - (degree + 1)) = cutoff by omega] at hequality
    simpa only [oddThetaDenominator, PowerSeries.coeff_mk, finite, argument]
      using hequality.symm
  have hcongruence (degree : ℕ) (first second third fourth :
      PowerSeries (LaurentPolynomial ℚ))
      (hfirst : ∀ earlier ≤ degree,
        PowerSeries.coeff earlier first = PowerSeries.coeff earlier second)
      (hsecond : ∀ earlier ≤ degree,
        PowerSeries.coeff earlier third = PowerSeries.coeff earlier fourth) :
      ∀ earlier ≤ degree, PowerSeries.coeff earlier (first * third) =
        PowerSeries.coeff earlier (second * fourth) := by
    intro earlier hearlier
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro pair hpair
    have := mem_antidiagonal.mp hpair
    rw [hfirst pair.1 (by omega), hsecond pair.2 (by omega)]
  have hderivatives (order degree cutoff : ℕ) (hlarge : degree < cutoff) :
      PowerSeries.coeff degree (derivative^[order] oddThetaDenominator) =
        PowerSeries.coeff degree (derivative^[order] (finite cutoff)) := by
    induction order with
    | zero => exact happroximation degree cutoff hlarge
    | succ order ih =>
        simp only [Function.iterate_succ_apply', hcoeff, ih]
  have hnumerator (degree cutoff : ℕ) (hlarge : degree < cutoff) :
      PowerSeries.coeff degree (numerator oddThetaDenominator) =
        PowerSeries.coeff degree (numerator (finite cutoff)) := by
    have hterm (order : ℕ) := fun earlier (hearlier : earlier ≤ degree) =>
      hderivatives order earlier cutoff (by omega)
    have hzeroth : ∀ earlier ≤ degree,
        PowerSeries.coeff earlier oddThetaDenominator = PowerSeries.coeff earlier (finite cutoff) :=
      fun earlier hearlier => happroximation earlier cutoff (by omega)
    have hpower (power : ℕ) : ∀ earlier ≤ degree,
        PowerSeries.coeff earlier (oddThetaDenominator ^ power) =
          PowerSeries.coeff earlier (finite cutoff ^ power) := by
      induction power with
      | zero => simp
      | succ power ih =>
          simp only [pow_succ]
          exact hcongruence degree _ _ _ _ ih hzeroth
    dsimp only [numerator]
    have hfirst : ∀ earlier ≤ degree,
        PowerSeries.coeff earlier (derivative oddThetaDenominator) =
          PowerSeries.coeff earlier (derivative (finite cutoff)) := by
      simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using hterm 1
    have hsecond : ∀ earlier ≤ degree,
        PowerSeries.coeff earlier (derivative (derivative oddThetaDenominator)) =
          PowerSeries.coeff earlier (derivative (derivative (finite cutoff))) := by
      simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using hterm 2
    have hthird : ∀ earlier ≤ degree,
        PowerSeries.coeff earlier (derivative (derivative (derivative oddThetaDenominator))) =
          PowerSeries.coeff earlier (derivative (derivative (derivative (finite cutoff)))) := by
      simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using hterm 3
    have hderivativePower : ∀ earlier ≤ degree,
        PowerSeries.coeff earlier (derivative oddThetaDenominator ^ 3) =
          PowerSeries.coeff earlier (derivative (finite cutoff) ^ 3) := by
      simp only [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, pow_zero, one_mul]
      exact hcongruence degree _ _ _ _
        (hcongruence degree _ _ _ _ hfirst hfirst) hfirst
    simp only [map_sub, map_add]
    rw [hcongruence degree _ _ _ _ hthird (hpower 2) degree le_rfl,
      hcongruence degree _ _ _ _
        (hcongruence degree _ _ _ _
          (hcongruence degree _ _ _ _ (fun _ _ => rfl) hsecond) hfirst)
        hzeroth degree le_rfl,
      hcongruence degree _ _ _ _ (fun _ _ => rfl) hderivativePower degree le_rfl]
  let base : PowerSeries ℚ := PowerSeries.X * (1 + PowerSeries.X) *
    (PowerSeries.invOneSubPow ℚ 3).val
  have hbase (index : ℕ) : PowerSeries.coeff index base = (index : ℚ) ^ 2 := by
    dsimp only [base]
    rw [show (PowerSeries.X : PowerSeries ℚ) * (1 + PowerSeries.X) =
      PowerSeries.X + PowerSeries.X ^ 2 by ring, add_mul, map_add]
    cases index with
    | zero => simp
    | succ index =>
        rw [PowerSeries.coeff_succ_X_mul]
        cases index with
        | zero => norm_num [PowerSeries.invOneSubPow, PowerSeries.coeff_X_pow_mul']
        | succ index =>
            rw [PowerSeries.coeff_X_pow_mul']
            simp only [show 2 ≤ index + 1 + 1 by omega, ite_true,
              show index + 1 + 1 - 2 = index by omega]
            simp only [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
              PowerSeries.coeff_mk, Nat.cast_choose_two, Nat.cast_add, Nat.cast_one]
            ring
  have hphi (spacing : ℕ) (hspacing : 0 < spacing) (location : ℤ) (degree : ℕ) :
      PowerSeries.coeff degree
          (phi (PowerSeries.X ^ spacing * PowerSeries.C (LaurentPolynomial.T location))) =
        if spacing ∣ degree then
          LaurentPolynomial.C (((degree / spacing : ℕ) : ℚ) ^ 2) *
            LaurentPolynomial.T ((degree / spacing : ℕ) * location)
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
      have hfirst := congrArg transfer (PowerSeries.invOneSubPow ℚ 3).inv_val
      have hsecond := PowerSeries.mul_invOfUnit (1 - input) 1 (by simp [hzero])
      rw [← mul_pow, hsecond, one_pow]
      simpa only [PowerSeries.invOneSubPow_inv_eq_one_sub_pow, map_mul, map_pow,
        map_sub, map_one, hinput] using hfirst
    have htransfer : transfer base = phi input := by
      simp only [base, map_mul, map_add, map_one, hinput, hinverse, phi]
    rw [← htransfer]
    dsimp only [transfer, RingHom.comp_apply]
    change PowerSeries.coeff degree
      (PowerSeries.expand spacing (by omega)
        (PowerSeries.rescale (LaurentPolynomial.T location)
          (PowerSeries.map LaurentPolynomial.C base))) = _
    rw [PowerSeries.coeff_expand]
    split_ifs with hdivides
    · rw [PowerSeries.coeff_rescale, PowerSeries.coeff_map, hbase,
        LaurentPolynomial.T_pow, mul_comm]
    · rfl
  let lambert : PowerSeries (LaurentPolynomial ℚ) := PowerSeries.mk fun degree =>
    ∑ index ∈ Finset.range (degree + 1),
      if 0 < index ∧ index ∣ degree ∧ Odd (degree / index) then
        LaurentPolynomial.C ((index : ℚ) ^ 2) *
          (LaurentPolynomial.T (index : ℤ) - LaurentPolynomial.T (-(index : ℤ)))
      else 0
  have htail (degree : ℕ) : PowerSeries.coeff degree (tail (degree + 1)) =
      PowerSeries.coeff degree lambert := by
    simp only [tail, argument, map_sum, map_sub]
    have hphiOdd (index : ℕ) (location : ℤ) := hphi (2 * index + 1) (by omega) location degree
    simp_rw [hphiOdd]
    simp only [lambert, PowerSeries.coeff_mk]
    have hsub (index : ℕ) :
        (if (2 * index + 1) ∣ degree then
          LaurentPolynomial.C (((degree / (2 * index + 1) : ℕ) : ℚ) ^ 2) *
            LaurentPolynomial.T ((degree / (2 * index + 1) : ℕ) * (1 : ℤ)) else 0) -
        (if (2 * index + 1) ∣ degree then
          LaurentPolynomial.C (((degree / (2 * index + 1) : ℕ) : ℚ) ^ 2) *
            LaurentPolynomial.T ((degree / (2 * index + 1) : ℕ) * (-1 : ℤ)) else 0) =
        if (2 * index + 1) ∣ degree then
          LaurentPolynomial.C (((degree / (2 * index + 1) : ℕ) : ℚ) ^ 2) *
            (LaurentPolynomial.T (degree / (2 * index + 1) : ℕ) -
              LaurentPolynomial.T (-((degree / (2 * index + 1) : ℕ) : ℤ))) else 0 := by
      split_ifs <;> simp only [mul_one, mul_neg_one, mul_sub, sub_zero]
    simp_rw [hsub]
    let source := (Finset.range (degree + 1)).filter (fun index => (2 * index + 1) ∣ degree)
    let target := (Finset.range (degree + 1)).filter
      (fun index => 0 < index ∧ index ∣ degree ∧ Odd (degree / index))
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    by_cases hzero : degree = 0
    · subst degree
      simp [source, target]
    have hpositive : 0 < degree := by omega
    change (∑ index ∈ source, _) = ∑ index ∈ target, _
    apply Finset.sum_bij (fun index _ => degree / (2 * index + 1))
    · intro index hindex
      have hdivides := (Finset.mem_filter.mp hindex).2
      have hbound : 2 * index + 1 ≤ degree := Nat.le_of_dvd hpositive hdivides
      have hquotient : 0 < degree / (2 * index + 1) := Nat.div_pos hbound (by omega)
      have hinverse : degree / (degree / (2 * index + 1)) = 2 * index + 1 :=
        Nat.div_div_self hdivides hzero
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by have := Nat.div_le_self degree (2 * index + 1); omega),
        hquotient, ?_, ?_⟩
      · exact Nat.div_dvd_of_dvd hdivides
      · rw [hinverse]
        exact ⟨index, by omega⟩
    · intro first hfirst second hsecond hequal
      have hfirstInverse := Nat.div_div_self (Finset.mem_filter.mp hfirst).2 hzero
      have hsecondInverse := Nat.div_div_self (Finset.mem_filter.mp hsecond).2 hzero
      rw [hequal, hsecondInverse] at hfirstInverse
      omega
    · intro index hindex
      obtain ⟨hrange, hpositiveIndex, hdivides, hodd⟩ := Finset.mem_filter.mp hindex
      obtain ⟨sourceIndex, hsourceIndex⟩ := hodd
      have hspacing : degree / index = 2 * sourceIndex + 1 := by omega
      have hinverse : degree / (degree / index) = index := Nat.div_div_self hdivides hzero
      refine ⟨sourceIndex, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr ?_, ?_⟩
        · have := Nat.div_le_self degree index
          omega
        · rw [← hspacing]
          exact Nat.div_dvd_of_dvd hdivides
      · rw [← hspacing, hinverse]
    · intro index _
      rfl
  have hphiVanish (degree index : ℕ) (location : ℤ) (hsmall : degree < 2 * index + 1) :
      PowerSeries.coeff degree (phi (argument location index)) = 0 := by
    rw [show phi (argument location index) =
      PowerSeries.X ^ (2 * index + 1) *
        (PowerSeries.C (LaurentPolynomial.T location) * (1 + argument location index) *
          PowerSeries.invOfUnit (1 - argument location index) 1 ^ 3) by
      dsimp only [phi, argument]; ring]
    rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have htailStable (degree cutoff : ℕ) (hlarge : degree < cutoff) :
      PowerSeries.coeff degree (tail cutoff) = PowerSeries.coeff degree (tail (degree + 1)) := by
    simp only [tail, map_sum, map_sub]
    apply (Finset.sum_subset (Finset.range_mono (by omega)) ?_).symm
    intro index _ hnot
    have hbound : degree + 1 ≤ index := by simpa only [Finset.mem_range, not_lt] using hnot
    rw [hphiVanish degree index 1 (by omega), hphiVanish degree index (-1) (by omega), sub_self]
  have hrhs (degree : ℕ) :
      PowerSeries.coeff degree (-(finite (degree + 1)) ^ 3 * tail (degree + 1)) =
        PowerSeries.coeff degree (-oddThetaDenominator ^ 3 * lambert) := by
    have htailApproximation (earlier : ℕ) (hearlier : earlier ≤ degree) :
        PowerSeries.coeff earlier (tail (degree + 1)) = PowerSeries.coeff earlier lambert := by
      rw [htailStable earlier (degree + 1) (by omega), htail earlier]
    have hpower (power : ℕ) : ∀ earlier ≤ degree,
        PowerSeries.coeff earlier (finite (degree + 1) ^ power) =
          PowerSeries.coeff earlier (oddThetaDenominator ^ power) := by
      induction power with
      | zero => simp
      | succ power ih =>
          simp only [pow_succ]
          apply hcongruence degree _ _ _ _ ih
          intro earlier hearlier
          exact (happroximation earlier (degree + 1) (by omega)).symm
    simp only [neg_mul, map_neg]
    exact congrArg (fun poly : LaurentPolynomial ℚ => -poly)
      (hcongruence degree _ _ _ _ (hpower 3) htailApproximation degree le_rfl)
  constructor
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, happroximation 0 1 (by omega)]
    simp [finite, argument]
  · simp (config := { zetaDelta := false }) only [hraw]
    change numerator oddThetaDenominator = -oddThetaDenominator ^ 3 * lambert
    apply PowerSeries.ext
    intro degree
    rw [hnumerator degree (degree + 1) (by omega), hfinite, hrhs]

end D5.S3.Combinatorics.InversionSeq.InversionSeq207OddLambert
