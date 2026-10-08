/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207SelfAdjoint
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207SelfAdjoint
   mirror-E: none(waiver:formal-constant-term-pairing)
   anchors: []
   utility: none
   digest: Finite exponent convolution and Pearson cancellation prove formal self-adjointness. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207Pearson

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207SelfAdjoint

open InversionSeq207Difference InversionSeq207Pearson

noncomputable def coefficientLift :
    LaurentSeries ℚ →+* LaurentSeries (LaurentPolynomial ℚ) where
  toFun series := series.map LaurentPolynomial.C
  map_zero' := HahnSeries.map_zero LaurentPolynomial.C.toZeroHom
  map_one' := by ext degree; simp [HahnSeries.map_coeff]
  map_add' _ _ := HahnSeries.map_add LaurentPolynomial.C.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul LaurentPolynomial.C.toNonUnitalRingHom

noncomputable def polynomialLift :
    LaurentPolynomial (LaurentSeries ℚ) →+* LaurentSeries (LaurentPolynomial ℚ) :=
  LaurentPolynomial.eval₂ coefficientLift
    (Units.map HahnSeries.C.toMonoidHom (unitOfInvertible (LaurentPolynomial.T 1)))

noncomputable def constantTerm : LaurentSeries (LaurentPolynomial ℚ) →+ LaurentSeries ℚ where
  toFun series := series.map ((Finsupp.applyAddHom (0 : ℤ)).comp
    AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)
  map_zero' := by ext degree; simp [HahnSeries.map_coeff]
  map_add' left right := by ext degree; simp [HahnSeries.map_coeff]

noncomputable def weightConstantTerm (poly : LaurentPolynomial (LaurentSeries ℚ)) :
    LaurentSeries ℚ :=
  constantTerm ((formalWeight : LaurentSeries (LaurentPolynomial ℚ)) * polynomialLift poly)

set_option maxHeartbeats 2400000 in
theorem formal_self_adjoint (first second firstOutput secondOutput :
    LaurentPolynomial (LaurentSeries ℚ))
    (hfirst :
      (1 - LaurentPolynomial.T 1 ^ 2) *
          (1 - LaurentPolynomial.C
            (((PowerSeries.X : PowerSeries ℚ) : LaurentSeries ℚ) ^ 2) *
            LaurentPolynomial.T 1 ^ 2) *
          (LaurentPolynomial.C (((PowerSeries.X : PowerSeries ℚ) : LaurentSeries ℚ) ^ 2) -
            LaurentPolynomial.T 1 ^ 2) * firstOutput =
        differenceNumerator ((PowerSeries.X : PowerSeries ℚ) : LaurentSeries ℚ)
          (Units.mk0 (((PowerSeries.X : PowerSeries ℚ) : LaurentSeries ℚ) ^ 2)
            (by exact pow_ne_zero 2 (by
              intro hzero
              have hequality := congrArg (fun series : LaurentSeries ℚ => series.coeff 1) hzero
              simp at hequality))) first)
    (hsecond :
      (1 - LaurentPolynomial.T 1 ^ 2) *
          (1 - LaurentPolynomial.C
            (((PowerSeries.X : PowerSeries ℚ) : LaurentSeries ℚ) ^ 2) *
            LaurentPolynomial.T 1 ^ 2) *
          (LaurentPolynomial.C (((PowerSeries.X : PowerSeries ℚ) : LaurentSeries ℚ) ^ 2) -
            LaurentPolynomial.T 1 ^ 2) * secondOutput =
        differenceNumerator ((PowerSeries.X : PowerSeries ℚ) : LaurentSeries ℚ)
          (Units.mk0 (((PowerSeries.X : PowerSeries ℚ) : LaurentSeries ℚ) ^ 2)
            (by exact pow_ne_zero 2 (by
              intro hzero
              have hequality := congrArg (fun series : LaurentSeries ℚ => series.coeff 1) hzero
              simp at hequality))) second) :
    weightConstantTerm (first * secondOutput) =
      weightConstantTerm (second * firstOutput) := by
  classical
  let rho : LaurentSeries ℚ := (PowerSeries.X : PowerSeries ℚ)
  have hrho : rho ≠ 0 := by
    intro hzero
    have hequality := congrArg (fun series : LaurentSeries ℚ => series.coeff 1) hzero
    simp [rho] at hequality
  let qUnit := Units.mk0 (rho ^ 2) (pow_ne_zero 2 hrho)
  let indeterminate : LaurentSeries (LaurentPolynomial ℚ) :=
    HahnSeries.C (LaurentPolynomial.T 1)
  let reverse : LaurentSeries (LaurentPolynomial ℚ) :=
    HahnSeries.C (LaurentPolynomial.T (-1))
  let parameter := coefficientLift rho
  let scalar := coefficientLift ((qUnit : LaurentSeries ℚ))
  let weight : LaurentSeries (LaurentPolynomial ℚ) := formalWeight
  let product : LaurentSeries (LaurentPolynomial ℚ) := pearsonProduct
  let reflected : LaurentSeries (LaurentPolynomial ℚ) :=
    product.map LaurentPolynomial.invert.toRingHom
  let reflection : LaurentSeries (LaurentPolynomial ℚ) →+*
      LaurentSeries (LaurentPolynomial ℚ) :=
    { toFun := fun series => series.map LaurentPolynomial.invert.toRingHom
      map_zero' := by ext degree; simp [HahnSeries.map_coeff]
      map_one' := by ext degree; simp [HahnSeries.map_coeff]
      map_add' := fun _ _ => HahnSeries.map_add LaurentPolynomial.invert.toAddMonoidHom
      map_mul' := fun _ _ => HahnSeries.map_mul LaurentPolynomial.invert.toNonUnitalRingHom }
  let column (location : ℤ) : LaurentPolynomial ℚ →+ ℚ :=
    (Finsupp.applyAddHom location).comp AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom
  let denominator := (1 - indeterminate ^ 2) * (1 - scalar * indeterminate ^ 2) *
    (scalar - indeterminate ^ 2)
  have hliftC (value : LaurentSeries ℚ) :
      polynomialLift (LaurentPolynomial.C value) = coefficientLift value := by
    simp [polynomialLift]
  have hliftT (location : ℤ) :
      polynomialLift (LaurentPolynomial.T location) =
        HahnSeries.C (LaurentPolynomial.T location) := by
    have hunit :
        ((unitOfInvertible (LaurentPolynomial.T 1) ^ location :
          (LaurentPolynomial ℚ)ˣ) : LaurentPolynomial ℚ) =
          LaurentPolynomial.T location := by
      cases location with
      | ofNat index => simp [zpow_natCast, unitOfInvertible, LaurentPolynomial.T_pow]
      | negSucc index =>
          simp [zpow_negSucc, unitOfInvertible, LaurentPolynomial.T_pow]
          congr 1
          omega
    simp only [polynomialLift, LaurentPolynomial.eval₂_T, ← map_zpow,
      Units.coe_map, hunit]
    rfl
  have hindeterminate : indeterminate * reverse = 1 := by
    change HahnSeries.C (LaurentPolynomial.T 1) * HahnSeries.C (LaurentPolynomial.T (-1)) = 1
    rw [← map_mul, ← LaurentPolynomial.T_add]
    norm_num
  have hbalance : weight * (1 - parameter * indeterminate) ^ 2 =
      product * (1 - indeterminate ^ 2) * (1 - scalar * indeterminate ^ 2) := by
    have hequality := congrArg (HahnSeries.ofPowerSeries ℤ (LaurentPolynomial ℚ))
      pearson_balance.2.2.2.1
    have hparameter : parameter = (PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)) := by
      apply HahnSeries.ext; funext degree
      by_cases hdegree : degree = 1 <;>
        simp [parameter, coefficientLift, rho, HahnSeries.map_coeff, hdegree]
    have hscalar : scalar = parameter ^ 2 := by
      simp [scalar, qUnit, parameter]
    simpa [weight, product, indeterminate, scalar, hscalar, hparameter,
      HahnSeries.C, HahnSeries.ofPowerSeries_C] using hequality
  have hreflection : weight.map LaurentPolynomial.invert.toRingHom = weight := by
    ext degree location
    by_cases hnegative : degree < 0
    · simp [weight, PowerSeries.coeff_coe, hnegative, HahnSeries.map_coeff]
    · obtain ⟨index, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ degree)
      simpa [weight, HahnSeries.map_coeff] using
        congrArg (fun poly : LaurentPolynomial ℚ => poly.coeff location)
          (pearson_balance.2.2.2.2 index)
  have hreverseBalance : weight * (1 - parameter * reverse) ^ 2 =
      reflected * (1 - reverse ^ 2) * (1 - scalar * reverse ^ 2) := by
    have hequality := congrArg reflection hbalance
    have hmapParameter : parameter.map LaurentPolynomial.invert.toRingHom = parameter := by
      ext degree
      simp [parameter, coefficientLift, HahnSeries.map_coeff]
    have hmapScalar : scalar.map LaurentPolynomial.invert.toRingHom = scalar := by
      ext degree
      simp [scalar, coefficientLift, HahnSeries.map_coeff]
    have hmapVariable : indeterminate.map LaurentPolynomial.invert.toRingHom = reverse := by
      apply HahnSeries.ext; funext degree
      by_cases hdegree : degree = 0 <;>
        simp [indeterminate, reverse, HahnSeries.map_coeff, hdegree]
    have hweight : reflection weight = weight := hreflection
    have hparameter : reflection parameter = parameter := hmapParameter
    have hscalar : reflection scalar = scalar := hmapScalar
    have hindeterminate : reflection indeterminate = reverse := hmapVariable
    have hproduct : reflection product = reflected := rfl
    simpa only [map_mul, map_sub, map_pow, map_one,
      hweight, hparameter, hscalar, hindeterminate, hproduct] using hequality
  have hdenominator : denominator ≠ 0 := by
    have hsquare : indeterminate ^ 2 = HahnSeries.C (LaurentPolynomial.T 2) := by
      change HahnSeries.C (LaurentPolynomial.T 1) ^ 2 =
        HahnSeries.C (LaurentPolynomial.T 2)
      rw [← map_pow, LaurentPolynomial.T_pow]
      norm_num
    have hscalar : scalar = HahnSeries.single 2 1 := by
      apply HahnSeries.ext; funext degree
      by_cases hdegree : degree = 2 <;>
        simp [scalar, coefficientLift, rho, qUnit, HahnSeries.map_coeff,
          HahnSeries.ofPowerSeries_X, HahnSeries.single_pow, hdegree]
    dsimp [denominator]
    apply mul_ne_zero
    · apply mul_ne_zero
      · intro hzero
        rw [hsquare] at hzero
        have hequality := congrArg (fun series : LaurentSeries (LaurentPolynomial ℚ) =>
          (series.coeff 0).coeff 2) hzero
        rw [HahnSeries.coeff_sub, HahnSeries.coeff_one] at hequality
        simp only [HahnSeries.C_apply, HahnSeries.coeff_single, HahnSeries.coeff_zero,
          if_true] at hequality
        change ((1 : LaurentPolynomial ℚ) - AddMonoidAlgebra.single 2 (1 : ℚ)).coeff 2 =
          0 at hequality
        have hone : (1 : LaurentPolynomial ℚ).coeff 2 = 0 := by
          change (AddMonoidAlgebra.single 0 (1 : ℚ)).coeff 2 = 0
          simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
          norm_num
        rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hone] at hequality
        norm_num only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
          AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Finsupp.single_apply,
          if_true, if_false, Int.reduceEq] at hequality
      · intro hzero
        have hequality := congrArg (fun series : LaurentSeries (LaurentPolynomial ℚ) =>
          (series.coeff 0).coeff 0) hzero
        norm_num [hscalar, hsquare, HahnSeries.C,
          HahnSeries.coeff_single_mul, HahnSeries.coeff_sub] at hequality
    · intro hzero
      rw [hscalar, hsquare] at hzero
      have hequality := congrArg (fun series : LaurentSeries (LaurentPolynomial ℚ) =>
        (series.coeff 0).coeff 2) hzero
      rw [HahnSeries.coeff_sub] at hequality
      simp only [HahnSeries.C_apply, HahnSeries.coeff_single, HahnSeries.coeff_zero] at hequality
      norm_num only [Int.reduceEq, if_false, zero_sub] at hequality
      change (-(AddMonoidAlgebra.single 2 (1 : ℚ))).coeff 2 = 0 at hequality
      norm_num only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply,
        AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_true] at hequality
  have haction (input output : LaurentPolynomial (LaurentSeries ℚ))
      (hequation :
        (1 - LaurentPolynomial.T 1 ^ 2) *
            (1 - LaurentPolynomial.C (qUnit : LaurentSeries ℚ) * LaurentPolynomial.T 1 ^ 2) *
            (LaurentPolynomial.C (qUnit : LaurentSeries ℚ) - LaurentPolynomial.T 1 ^ 2) *
            output = differenceNumerator rho qUnit input) :
      weight * polynomialLift output =
        product * (polynomialLift (laurentShift qUnit input) - polynomialLift input) +
          reflected * (polynomialLift (laurentShift qUnit⁻¹ input) - polynomialLift input) := by
    have hequality := congrArg polynomialLift hequation
    simp only [differenceNumerator, map_mul, map_sub, map_add, map_one, map_pow,
      hliftC, hliftT] at hequality
    change denominator * polynomialLift output =
      (1 - parameter * indeterminate) ^ 2 * (scalar - indeterminate ^ 2) *
          (polynomialLift (laurentShift qUnit input) - polynomialLift input) +
        (indeterminate - parameter) ^ 2 * indeterminate ^ 2 * (1 - scalar * indeterminate ^ 2) *
          (polynomialLift (laurentShift qUnit⁻¹ input) - polynomialLift input) at hequality
    apply mul_left_cancel₀ hdenominator
    have hfirstFactor :
        weight * (1 - parameter * indeterminate) ^ 2 * (scalar - indeterminate ^ 2) =
          denominator * product := by
      rw [hbalance]
      dsimp [denominator]
      ring
    have hsecondFactor :
        weight * (indeterminate - parameter) ^ 2 * indeterminate ^ 2 *
            (1 - scalar * indeterminate ^ 2) = denominator * reflected := by
      have hindeterminateSquared : indeterminate ^ 2 * reverse ^ 2 = 1 := by
        rw [← mul_pow, hindeterminate, one_pow]
      have hinput : (indeterminate - parameter) ^ 2 =
          indeterminate ^ 2 * (1 - parameter * reverse) ^ 2 := by
        calc
          _ = (indeterminate * (1 - parameter * reverse)) ^ 2 := by
            congr 1
            linear_combination parameter * hindeterminate
          _ = _ := by ring
      rw [hinput]
      calc
        _ = (weight * (1 - parameter * reverse) ^ 2) * indeterminate ^ 4 *
            (1 - scalar * indeterminate ^ 2) := by ring
        _ = reflected * (1 - reverse ^ 2) * (1 - scalar * reverse ^ 2) *
            indeterminate ^ 4 * (1 - scalar * indeterminate ^ 2) := by rw [hreverseBalance]
        _ = denominator * reflected := by
          dsimp [denominator]
          linear_combination reflected * (1 - scalar * indeterminate ^ 2) *
            (scalar * (indeterminate ^ 2 * reverse ^ 2 + 1) -
              (1 + scalar) * indeterminate ^ 2) * hindeterminateSquared
    calc
      _ = weight * (denominator * polynomialLift output) := by ring
      _ = weight * _ := by rw [hequality]
      _ = (weight * (1 - parameter * indeterminate) ^ 2 * (scalar - indeterminate ^ 2)) *
            (polynomialLift (laurentShift qUnit input) - polynomialLift input) +
          (weight * (indeterminate - parameter) ^ 2 * indeterminate ^ 2 *
              (1 - scalar * indeterminate ^ 2)) *
            (polynomialLift (laurentShift qUnit⁻¹ input) - polynomialLift input) := by ring
      _ = _ := by rw [hfirstFactor, hsecondFactor]; ring
  have hfirstAction := haction first firstOutput hfirst
  have hsecondAction := haction second secondOutput hsecond
  have hfiniteConvolution (left right : LaurentPolynomial (LaurentSeries ℚ)) :
      constantTerm (product * polynomialLift left * polynomialLift (laurentShift qUnit right)) =
        constantTerm (reflected * polynomialLift right *
          polynomialLift (laurentShift qUnit⁻¹ left)) := by
    induction left using LaurentPolynomial.induction_on' with
    | add left right hleft hright =>
        simp only [map_add, mul_add, add_mul, hleft, hright]
    | C_mul_T location value =>
        induction right using LaurentPolynomial.induction_on' with
        | add left right hleft hright =>
            simp only [map_add, mul_add, add_mul, hleft, hright]
        | C_mul_T other coefficient =>
            have hshift (scale : (LaurentSeries ℚ)ˣ) (index : ℤ) :
                laurentShift scale (LaurentPolynomial.T index) =
                  LaurentPolynomial.C ((scale : LaurentSeries ℚ) ^ index) *
                    LaurentPolynomial.T index := by
              have hunit :
                  ((unitOfInvertible (LaurentPolynomial.T 1) ^ index :
                    (LaurentPolynomial (LaurentSeries ℚ))ˣ) :
                    LaurentPolynomial (LaurentSeries ℚ)) = LaurentPolynomial.T index := by
                cases index with
                | ofNat count =>
                    simp [zpow_natCast, unitOfInvertible, LaurentPolynomial.T_pow]
                | negSucc count =>
                    simp [zpow_negSucc, unitOfInvertible, LaurentPolynomial.T_pow]
                    congr 1
                    omega
              simp only [laurentShift, LaurentPolynomial.eval₂_T, mul_zpow, Units.val_mul]
              rw [← map_zpow, Units.coe_map, Units.val_zpow_eq_zpow_val, hunit]
              rfl
            have hshiftC (scale : (LaurentSeries ℚ)ˣ) (value : LaurentSeries ℚ) :
                laurentShift scale (LaurentPolynomial.C value) =
                  LaurentPolynomial.C value := by simp [laurentShift]
            have hscalarTerm (value : LaurentSeries ℚ)
                (series : LaurentSeries (LaurentPolynomial ℚ)) :
                constantTerm (coefficientLift value * series) = value * constantTerm series := by
              apply HahnSeries.ext; funext degree
              change ((coefficientLift value * series).coeff degree).coeff 0 =
                (value * constantTerm series).coeff degree
              have hliftSupport : (coefficientLift value).support ⊆ value.support := by
                intro index hindex
                rw [HahnSeries.mem_support] at hindex ⊢
                change LaurentPolynomial.C (value.coeff index) ≠ 0 at hindex
                intro hzero
                exact hindex (by rw [hzero, map_zero])
              have htermSupport : (constantTerm series).support ⊆ series.support := by
                intro index hindex
                rw [HahnSeries.mem_support] at hindex ⊢
                change (series.coeff index).coeff 0 ≠ 0 at hindex
                intro hzero
                exact hindex (by rw [hzero]; rfl)
              rw [HahnSeries.coeff_mul_left' (x := coefficientLift value) (y := series)
                  value.isPWO_support hliftSupport,
                HahnSeries.coeff_mul_right' (x := value) (y := constantTerm series)
                  series.isPWO_support htermSupport]
              simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
              apply Finset.sum_congr rfl
              intro pair _
              change (LaurentPolynomial.C (value.coeff pair.1) * series.coeff pair.2).coeff 0 =
                value.coeff pair.1 * (series.coeff pair.2).coeff 0
              change (AddMonoidAlgebra.single 0 (value.coeff pair.1) *
                series.coeff pair.2).coeff 0 =
                  value.coeff pair.1 * (series.coeff pair.2).coeff 0
              simp only [AddMonoidAlgebra.coeff_single_mul_apply,
                neg_zero, zero_add]
            have hshiftTerm (series : LaurentSeries (LaurentPolynomial ℚ)) (index : ℤ) :
                constantTerm (series * HahnSeries.C (LaurentPolynomial.T index)) =
                  series.map (column (-index)) := by
              apply HahnSeries.ext; funext degree
              change ((series * HahnSeries.single 0 (LaurentPolynomial.T index)).coeff
                degree).coeff 0 = (series.coeff degree).coeff (-index)
              simp only [HahnSeries.coeff_mul_single, sub_zero, LaurentPolynomial.T,
                AddMonoidAlgebra.coeff_mul_single_apply, zero_add, mul_one]
            have hmonomialTerm (series : LaurentSeries (LaurentPolynomial ℚ))
                (value : LaurentSeries ℚ) (index : ℤ) :
                constantTerm (series * coefficientLift value *
                    HahnSeries.C (LaurentPolynomial.T index)) =
                  value * series.map (column (-index)) := by
              rw [show series * coefficientLift value *
                  HahnSeries.C (LaurentPolynomial.T index) =
                  coefficientLift value *
                    (series * HahnSeries.C (LaurentPolynomial.T index)) by ring,
                hscalarTerm, hshiftTerm]
            have hcolumns (index : ℤ) :
                product.map (column (-index)) =
                  (qUnit : LaurentSeries ℚ) ^ (-index) *
                    product.map (column index) := by
              have hequality := pearson_balance.2.1 index
              have hcolumn (index : ℤ) :
                  product.map (column index) =
                    (PowerSeries.mk (fun degree =>
                      (PowerSeries.coeff degree pearsonProduct).coeff index) :
                      LaurentSeries ℚ) := by
                apply HahnSeries.ext; funext degree
                by_cases hnegative : degree < 0
                · simp [product, HahnSeries.map_coeff, PowerSeries.coeff_coe, hnegative,
                    column]
                · obtain ⟨count, rfl⟩ :=
                    Int.eq_ofNat_of_zero_le (by omega : 0 ≤ degree)
                  simp [product, HahnSeries.map_coeff, column]
              have hpower : (qUnit : LaurentSeries ℚ) ^ (-index) =
                  HahnSeries.single (-(2 * index)) 1 := by
                simp only [qUnit, Units.val_mk0, ← zpow_natCast, ← zpow_mul]
                change rho ^ ((2 : ℤ) * -index) = HahnSeries.single (-(2 * index)) 1
                rw [show (2 : ℤ) * -index = -(2 * index) by ring]
                rw [show rho = HahnSeries.single 1 1 by simp [rho]]
                exact (RatFunc.single_zpow _).symm
              rw [hcolumn, hcolumn, hpower]
              exact hequality
            have hreflectedColumn (index : ℤ) :
                reflected.map (column index) =
                  product.map (column (-index)) := by
              apply HahnSeries.ext; funext degree
              simp [reflected, HahnSeries.map_coeff, column]
            simp only [map_mul, hshift, hshiftC, hliftC, hliftT]
            have hcombine (series : LaurentSeries (LaurentPolynomial ℚ))
                (scale : LaurentSeries ℚ) (index other : ℤ) :
                series * (coefficientLift value * HahnSeries.C (LaurentPolynomial.T index)) *
                    (coefficientLift coefficient *
                      (coefficientLift scale * HahnSeries.C (LaurentPolynomial.T other))) =
                  series * coefficientLift (value * coefficient * scale) *
                    HahnSeries.C (LaurentPolynomial.T (index + other)) := by
              rw [LaurentPolynomial.T_add, map_mul, map_mul, map_mul]
              ring
            rw [hcombine, hmonomialTerm]
            rw [show reflected *
                  (coefficientLift coefficient * HahnSeries.C (LaurentPolynomial.T other)) *
                  (coefficientLift value *
                    (coefficientLift
                        (((qUnit⁻¹ : (LaurentSeries ℚ)ˣ) : LaurentSeries ℚ) ^ location) *
                      HahnSeries.C (LaurentPolynomial.T location))) =
                  reflected * coefficientLift
                    (value * coefficient * ((qUnit : LaurentSeries ℚ)⁻¹ ^ location)) *
                    HahnSeries.C (LaurentPolynomial.T (location + other)) by
                  simp only [Units.val_inv_eq_inv_val]
                  rw [LaurentPolynomial.T_add, map_mul, map_mul, map_mul]
                  ring,
              hmonomialTerm, hreflectedColumn, neg_neg, hcolumns]
            rw [inv_zpow, ← zpow_neg]
            have hpowers : (qUnit : LaurentSeries ℚ) ^ other *
                (qUnit : LaurentSeries ℚ) ^ (-(location + other)) =
                  (qUnit : LaurentSeries ℚ) ^ (-location) := by
              rw [← zpow_add₀ (Units.ne_zero qUnit)]
              congr 1
              omega
            calc
              _ = value * coefficient *
                  ((qUnit : LaurentSeries ℚ) ^ other *
                    (qUnit : LaurentSeries ℚ) ^ (-(location + other))) *
                  product.map (column (location + other)) := by ring
              _ = _ := by rw [hpowers]
  unfold weightConstantTerm
  rw [polynomialLift.map_mul, polynomialLift.map_mul]
  change constantTerm (weight * (polynomialLift first * polynomialLift secondOutput)) =
    constantTerm (weight * (polynomialLift second * polynomialLift firstOutput))
  have hfirstShift := hfiniteConvolution first second
  have hsecondShift := hfiniteConvolution second first
  calc
    _ = constantTerm (polynomialLift first * (weight * polynomialLift secondOutput)) := by
      exact congrArg constantTerm (by ring)
    _ = _ := by rw [hsecondAction]
    _ = constantTerm (product * polynomialLift first *
          polynomialLift (laurentShift qUnit second)) +
        constantTerm (reflected * polynomialLift first *
          polynomialLift (laurentShift qUnit⁻¹ second)) -
        constantTerm (product * polynomialLift first * polynomialLift second) -
        constantTerm (reflected * polynomialLift first * polynomialLift second) := by
      rw [show polynomialLift first *
          (product * (polynomialLift (laurentShift qUnit second) - polynomialLift second) +
            reflected * (polynomialLift (laurentShift qUnit⁻¹ second) - polynomialLift second)) =
          product * polynomialLift first * polynomialLift (laurentShift qUnit second) +
            reflected * polynomialLift first * polynomialLift (laurentShift qUnit⁻¹ second) -
            product * polynomialLift first * polynomialLift second -
            reflected * polynomialLift first * polynomialLift second by ring]
      simp only [map_add, map_sub]
    _ = constantTerm (product * polynomialLift second *
          polynomialLift (laurentShift qUnit first)) +
        constantTerm (reflected * polynomialLift second *
          polynomialLift (laurentShift qUnit⁻¹ first)) -
        constantTerm (product * polynomialLift second * polynomialLift first) -
        constantTerm (reflected * polynomialLift second * polynomialLift first) := by
      rw [hfirstShift, ← hsecondShift]
      have hproduct : product * polynomialLift first * polynomialLift second =
          product * polynomialLift second * polynomialLift first := by ring
      have hreflected : reflected * polynomialLift first * polynomialLift second =
          reflected * polynomialLift second * polynomialLift first := by ring
      rw [hproduct, hreflected]
      ring
    _ = constantTerm (polynomialLift second *
          (product * (polynomialLift (laurentShift qUnit first) - polynomialLift first) +
            reflected *
              (polynomialLift (laurentShift qUnit⁻¹ first) - polynomialLift first))) := by
      rw [show polynomialLift second *
          (product * (polynomialLift (laurentShift qUnit first) - polynomialLift first) +
            reflected * (polynomialLift (laurentShift qUnit⁻¹ first) - polynomialLift first)) =
          product * polynomialLift second * polynomialLift (laurentShift qUnit first) +
            reflected * polynomialLift second * polynomialLift (laurentShift qUnit⁻¹ first) -
            product * polynomialLift second * polynomialLift first -
            reflected * polynomialLift second * polynomialLift first by ring]
      simp only [map_add, map_sub]
    _ = _ := by rw [← hfirstAction]; exact congrArg constantTerm (by ring)

end D5.S3.Combinatorics.InversionSeq.InversionSeq207SelfAdjoint
