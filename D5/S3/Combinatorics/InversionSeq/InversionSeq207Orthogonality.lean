/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207Orthogonality
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207Orthogonality
   mirror-E: none(waiver:formal-polynomial-norm-induction)
   anchors: []
   utility: none
   digest: Spectral separation and finite cutoffs prove norms and generating contractions. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207SelfAdjoint
import D5.S3.Combinatorics.InversionSeq.InversionSeq207Eigen
import D5.S3.Combinatorics.InversionSeq.InversionSeq207Resolvent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207Orthogonality

open InversionSeq207Polynomials InversionSeq207SelfAdjoint InversionSeq207Pearson
open InversionSeq207Resolvent

set_option maxHeartbeats 1200000 in
theorem polynomial_orthogonality (first second : ℕ) :
    (weightConstantTerm
        (AddMonoidAlgebra.mapRingHom ℤ (HahnSeries.ofPowerSeries ℤ ℚ)
            (PowerSeries.coeff first polynomialGenerator) *
          AddMonoidAlgebra.mapRingHom ℤ (HahnSeries.ofPowerSeries ℤ ℚ)
            (PowerSeries.coeff second polynomialGenerator)) =
      if first = second then weightConstantTerm 1 else 0) ∧
    (0 < first → 0 < second →
      (1 - ((PowerSeries.X : PowerSeries ℚ) : LaurentSeries ℚ) ^ (first + second)) *
          constantTerm ((formalWeight : LaurentSeries (LaurentPolynomial ℚ)) *
            ((polynomialSpecialization first : LaurentSeries (LaurentPolynomial ℚ)) *
              (polynomialSpecialization second : LaurentSeries (LaurentPolynomial ℚ)))) =
        weightConstantTerm 1) := by
  classical
  let rho : LaurentSeries ℚ := (PowerSeries.X : PowerSeries ℚ)
  have hrho : rho ≠ 0 := by
    intro hzero
    have hequality := congrArg (fun series : LaurentSeries ℚ => series.coeff 1) hzero
    simp [rho] at hequality
  let qUnit := Units.mk0 (rho ^ 2) (pow_ne_zero 2 hrho)
  let transfer := AddMonoidAlgebra.mapRingHom ℤ (HahnSeries.ofPowerSeries ℤ ℚ)
  let poly := fun index => transfer (PowerSeries.coeff index polynomialGenerator)
  let moment := fun left right => weightConstantTerm (poly left * poly right)
  have hscalarTerm (value : LaurentSeries ℚ)
      (series : LaurentSeries (LaurentPolynomial ℚ)) :
      constantTerm (coefficientLift value * series) = value * constantTerm series := by
    apply HahnSeries.ext
    funext degree
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
    change (AddMonoidAlgebra.single 0 (value.coeff pair.1) * series.coeff pair.2).coeff 0 =
      value.coeff pair.1 * (series.coeff pair.2).coeff 0
    simp only [AddMonoidAlgebra.coeff_single_mul_apply, neg_zero, zero_add]
  have hlinear (value : LaurentSeries ℚ) (input : LaurentPolynomial (LaurentSeries ℚ)) :
      weightConstantTerm (LaurentPolynomial.C value * input) =
        value * weightConstantTerm input := by
    unfold weightConstantTerm
    rw [polynomialLift.map_mul]
    have hlift : polynomialLift (LaurentPolynomial.C value) = coefficientLift value := by
      simp [polynomialLift]
    rw [hlift]
    rw [show (formalWeight : LaurentSeries (LaurentPolynomial ℚ)) *
        (coefficientLift value * polynomialLift input) =
        coefficientLift value *
          ((formalWeight : LaurentSeries (LaurentPolynomial ℚ)) * polynomialLift input)
        by ring, hscalarTerm]
  have hsub (left right : LaurentPolynomial (LaurentSeries ℚ)) :
      weightConstantTerm (left - right) = weightConstantTerm left - weightConstantTerm right :=
    by simp [weightConstantTerm, map_sub, mul_sub]
  have hzero : weightConstantTerm 0 = 0 := by simp [weightConstantTerm]
  have hsymmetry (left right : ℕ) : moment left right = moment right left := by
    dsimp [moment]
    rw [mul_comm]
  have hpower (index : ℕ) : (qUnit : LaurentSeries ℚ)⁻¹ ^ index =
      HahnSeries.single (-(2 * (index : ℤ))) 1 := by
    simp only [qUnit, Units.val_mk0, inv_pow, ← pow_mul]
    rw [show rho = HahnSeries.single 1 1 by simp [rho]]
    simp only [HahnSeries.single_pow, one_pow, HahnSeries.inv_single, inv_one,
      nsmul_eq_mul]
    norm_num [mul_comm]
  have hoffdiagonal (left right : ℕ) (hdifferent : left ≠ right) : moment left right = 0 := by
    let leftValue := (qUnit : LaurentSeries ℚ)⁻¹ ^ left - 1
    let rightValue := (qUnit : LaurentSeries ℚ)⁻¹ ^ right - 1
    have hleft := polynomial_system.{0}.2.2.2.2.2.2
      (HahnSeries.ofPowerSeries ℤ ℚ) hrho left
    have hright := polynomial_system.{0}.2.2.2.2.2.2
      (HahnSeries.ofPowerSeries ℤ ℚ) hrho right
    have hself := formal_self_adjoint (poly left) (poly right)
      (LaurentPolynomial.C leftValue * poly left)
      (LaurentPolynomial.C rightValue * poly right) hleft.symm hright.symm
    have hproducts (value : LaurentSeries ℚ) (first second :
        LaurentPolynomial (LaurentSeries ℚ)) :
        first * (LaurentPolynomial.C value * second) =
          LaurentPolynomial.C value * (first * second) := by ring
    rw [hproducts, hproducts, hlinear, hlinear] at hself
    change rightValue * moment left right = leftValue * moment right left at hself
    rw [hsymmetry right left] at hself
    have heigenvalues : rightValue ≠ leftValue := by
      intro hequal
      have hpowers : (qUnit : LaurentSeries ℚ)⁻¹ ^ right =
          (qUnit : LaurentSeries ℚ)⁻¹ ^ left := by simpa [rightValue, leftValue] using hequal
      rw [hpower, hpower] at hpowers
      have hequality := congrArg (fun series : LaurentSeries ℚ =>
        series.coeff (-(2 * (left : ℤ)))) hpowers
      have hexponents : -(2 * (right : ℤ)) ≠ -(2 * (left : ℤ)) := by omega
      simp [Ne.symm hexponents] at hequality
    have hcharged : (rightValue - leftValue) * moment left right = 0 := by
      rw [sub_mul, hself, sub_self]
    exact (mul_eq_zero.mp hcharged).resolve_left (sub_ne_zero.mpr heigenvalues)
  have hconstant : poly 0 = 1 := by
    change transfer (PowerSeries.coeff 0 polynomialGenerator) = 1
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, polynomial_system.{0}.1, map_one]
  have hrecurrence (index : ℕ) :
      LaurentPolynomial.C (1 - (qUnit : LaurentSeries ℚ) ^ (index + 1)) * poly (index + 1) =
        (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) -
          LaurentPolynomial.C (2 * rho * (qUnit : LaurentSeries ℚ) ^ index)) * poly index -
          LaurentPolynomial.C (1 - (qUnit : LaurentSeries ℚ) ^ index) *
            (if index = 0 then 0 else poly (index - 1)) := by
    have hequality := congrArg transfer (polynomial_system.{0}.2.1 index)
    have htransferC (value : PowerSeries ℚ) :
        transfer (LaurentPolynomial.C value) =
          LaurentPolynomial.C (value : LaurentSeries ℚ) :=
      AddMonoidAlgebra.mapRingHom_single (HahnSeries.ofPowerSeries ℤ ℚ) 0 value
    have htransferT (location : ℤ) : transfer (LaurentPolynomial.T location) =
        LaurentPolynomial.T location := by
      simpa only [transfer, LaurentPolynomial.T, map_one] using
        AddMonoidAlgebra.mapRingHom_single (HahnSeries.ofPowerSeries ℤ ℚ) location 1
    have hpowers (index : ℕ) :
        ((PowerSeries.X ^ (2 * index) : PowerSeries ℚ) : LaurentSeries ℚ) =
          (qUnit : LaurentSeries ℚ) ^ index := by simp [qUnit, rho, pow_mul]
    have hodd (index : ℕ) :
        ((PowerSeries.X ^ (2 * index + 1) : PowerSeries ℚ) : LaurentSeries ℚ) =
          rho * (qUnit : LaurentSeries ℚ) ^ index := by
      simp [qUnit, rho, pow_add, pow_mul, mul_comm]
    by_cases hindex : index = 0
    all_goals
      simp only [hindex, if_true, if_false, map_mul, map_sub, map_add, map_one,
        map_ofNat, htransferC, htransferT, hpowers, hodd, map_zero] at hequality
      simp only [hindex, if_true, if_false]
      convert hequality using 1 <;> dsimp [poly] <;>
        simp only [map_sub, map_mul, map_one, map_ofNat] <;> ring
  have hdiagonal (index : ℕ) : moment index index = weightConstantTerm 1 := by
    induction index with
    | zero => simp [moment, hconstant]
    | succ index ih =>
        let slope : LaurentPolynomial (LaurentSeries ℚ) :=
          LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)
        let factor := 1 - (qUnit : LaurentSeries ℚ) ^ (index + 1)
        have hfirst := congrArg (fun input => weightConstantTerm (input * poly (index + 1)))
          (hrecurrence index)
        have hsecond := congrArg (fun input => weightConstantTerm (input * poly index))
          (hrecurrence (index + 1))
        have hbefore : weightConstantTerm
            ((if index = 0 then 0 else poly (index - 1)) * poly (index + 1)) = 0 := by
          split_ifs with hindex
          · simp [hzero]
          · exact hoffdiagonal _ _ (by omega)
        have hafter : moment (index + 2) index = 0 := hoffdiagonal _ _ (by omega)
        have hcross : moment index (index + 1) = 0 := hoffdiagonal _ _ (by omega)
        have hcrossReverse : moment (index + 1) index = 0 := hoffdiagonal _ _ (by omega)
        have hexpand (value : LaurentSeries ℚ) (base previous next :
            LaurentPolynomial (LaurentSeries ℚ)) :
            ((slope - LaurentPolynomial.C value) * base - previous) * next =
              slope * base * next - LaurentPolynomial.C value * (base * next) -
                previous * next := by ring
        rw [hexpand, hsub, hsub] at hfirst
        simp only [mul_assoc, hlinear, hbefore] at hfirst
        have hfirstValue : factor * moment (index + 1) (index + 1) =
            weightConstantTerm (slope * poly index * poly (index + 1)) := by
          simpa [moment, factor, slope, mul_assoc, hlinear, hcross] using hfirst
        rw [hexpand, hsub, hsub] at hsecond
        simp only [show index + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel,
          mul_assoc, hlinear] at hsecond
        have hsecondValue : weightConstantTerm (slope * poly index * poly (index + 1)) =
            factor * moment index index := by
          have hcommute : slope * (poly (index + 1) * poly index) =
              slope * (poly index * poly (index + 1)) := by ring
          rw [hcommute] at hsecond
          dsimp [moment] at hafter hcrossReverse
          rw [show index + 1 + 1 = index + 2 by omega] at hsecond
          rw [hafter, hcrossReverse] at hsecond
          simp only [mul_zero, sub_zero] at hsecond
          have hsecondZero :
              weightConstantTerm (slope * poly index * poly (index + 1)) -
                factor * moment index index = 0 := by
            simpa only [factor, moment, mul_assoc] using hsecond.symm
          exact sub_eq_zero.mp hsecondZero
        have hfactor : factor ≠ 0 := by
          intro hzero
          have hequality := congrArg (fun series : LaurentSeries ℚ => series.coeff 0) hzero
          have hpower : (qUnit : LaurentSeries ℚ) ^ (index + 1) =
              HahnSeries.single (2 * ((index + 1 : ℕ) : ℤ)) 1 := by
            simp [qUnit, rho, HahnSeries.single_pow, mul_comm]
          simp [factor, hpower, HahnSeries.coeff_sub,
            show (index : ℤ) + 1 ≠ 0 by omega] at hequality
        apply mul_left_cancel₀ hfactor
        rw [hfirstValue, hsecondValue, ih]
  have horthogonal (left right : ℕ) : moment left right =
      if left = right then weightConstantTerm 1 else 0 := by
    split_ifs with hequal
    · subst right
      exact hdiagonal left
    · exact hoffdiagonal left right hequal
  refine ⟨horthogonal first second, ?_⟩
  intro hfirst hsecond
  let promote := HahnSeries.ofPowerSeries ℤ (LaurentPolynomial ℚ)
  let promoteQ := HahnSeries.ofPowerSeries ℤ ℚ
  let scalar := (PowerSeries.map LaurentPolynomial.C :
    PowerSeries ℚ →+* PowerSeries (LaurentPolynomial ℚ))
  let transpose : LaurentPolynomial (PowerSeries ℚ) →+*
      PowerSeries (LaurentPolynomial ℚ) :=
    LaurentPolynomial.eval₂ scalar
      (Units.map PowerSeries.C.toMonoidHom (unitOfInvertible (LaurentPolynomial.T 1)))
  let coefficients := fun index => transpose (PowerSeries.coeff index polynomialGenerator)
  let partialPolynomial := fun power cutoff =>
    ∑ index ∈ Finset.range cutoff,
      scalar (PowerSeries.X ^ (power * index)) * coefficients index
  let partialScalar := fun cutoff =>
    ∑ index ∈ Finset.range cutoff, (PowerSeries.X : PowerSeries ℚ) ^
      ((first + second) * index)
  let geometric : PowerSeries ℚ := PowerSeries.mk fun degree =>
    ∑ index ∈ Finset.range (degree + 1),
      PowerSeries.coeff degree (PowerSeries.X ^ ((first + second) * index) : PowerSeries ℚ)
  let zeroth : PowerSeries ℚ := PowerSeries.mk fun degree =>
    (PowerSeries.coeff degree formalWeight).coeff 0
  have hscalar (input : PowerSeries ℚ) :
      promote (scalar input) = coefficientLift (promoteQ input) := by
    apply HahnSeries.ext
    funext degree
    by_cases hnegative : degree < 0
    · simp [promote, scalar, coefficientLift, HahnSeries.map_coeff,
        PowerSeries.coeff_coe, hnegative, promoteQ]
    · obtain ⟨count, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ degree)
      simp [promote, promoteQ, scalar, coefficientLift, HahnSeries.map_coeff]
  have hunit (location : ℤ) :
      ((unitOfInvertible (LaurentPolynomial.T 1) ^ location :
        (LaurentPolynomial ℚ)ˣ) : LaurentPolynomial ℚ) = LaurentPolynomial.T location := by
    cases location with
    | ofNat index => simp [zpow_natCast, unitOfInvertible, LaurentPolynomial.T_pow]
    | negSucc index =>
        simp [zpow_negSucc, unitOfInvertible, LaurentPolynomial.T_pow]
        congr 1
        omega
  have htranspose (input : LaurentPolynomial (PowerSeries ℚ)) :
      promote (transpose input) = polynomialLift (transfer input) := by
    have htransferC (value : PowerSeries ℚ) :
        transfer (LaurentPolynomial.C value) = LaurentPolynomial.C (promoteQ value) :=
      AddMonoidAlgebra.mapRingHom_single promoteQ 0 value
    have htransferT (location : ℤ) : transfer (LaurentPolynomial.T location) =
        LaurentPolynomial.T location := by
      simpa only [transfer, LaurentPolynomial.T, map_one] using
        AddMonoidAlgebra.mapRingHom_single promoteQ location 1
    have htransposeC (value : PowerSeries ℚ) :
        transpose (LaurentPolynomial.C value) = scalar value := by simp [transpose]
    have htransposeT (location : ℤ) : transpose (LaurentPolynomial.T location) =
        PowerSeries.C (LaurentPolynomial.T location) := by
      simp only [transpose, LaurentPolynomial.eval₂_T, ← map_zpow, Units.coe_map, hunit]
      rfl
    have hliftC (value : LaurentSeries ℚ) :
        polynomialLift (LaurentPolynomial.C value) = coefficientLift value := by
      simp [polynomialLift]
    have hliftT (location : ℤ) : polynomialLift (LaurentPolynomial.T location) =
        HahnSeries.C (LaurentPolynomial.T location) := by
      simp only [polynomialLift, LaurentPolynomial.eval₂_T, ← map_zpow, Units.coe_map, hunit]
      rfl
    induction input using LaurentPolynomial.induction_on with
    | h_C value => rw [htransposeC, htransferC, hliftC, hscalar]
    | h_add hleft hright => simp only [map_add, hleft, hright]
    | h_C_mul_T index value _ =>
        simp only [map_mul, htransferC, htransferT, htransposeC, htransposeT,
          hliftC, hliftT, hscalar]
        rw [HahnSeries.ofPowerSeries_C]
    | h_C_mul_T_Z index value _ =>
        simp only [map_mul, htransferC, htransferT, htransposeC, htransposeT,
          hliftC, hliftT, hscalar]
        rw [HahnSeries.ofPowerSeries_C]
  have hzeroth : weightConstantTerm 1 = promoteQ zeroth := by
    apply HahnSeries.ext
    funext degree
    by_cases hnegative : degree < 0
    · simp [weightConstantTerm, constantTerm, HahnSeries.map_coeff, promoteQ,
        PowerSeries.coeff_coe, hnegative]
    · obtain ⟨count, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ degree)
      simp [weightConstantTerm, constantTerm, HahnSeries.map_coeff, promoteQ, zeroth]
  have hsingle (left right : ℕ) :
      constantTerm (promote formalWeight *
        (promote (scalar (PowerSeries.X ^ (first * left))) * promote (coefficients left) *
          (promote (scalar (PowerSeries.X ^ (second * right))) *
            promote (coefficients right)))) =
        promoteQ (PowerSeries.X ^ (first * left + second * right)) *
          (if left = right then weightConstantTerm 1 else 0) := by
    simp only [coefficients, htranspose, hscalar]
    rw [show promote formalWeight *
        (coefficientLift (promoteQ (PowerSeries.X ^ (first * left))) *
          polynomialLift (poly left) *
          (coefficientLift (promoteQ (PowerSeries.X ^ (second * right))) *
            polynomialLift (poly right))) =
        coefficientLift (promoteQ (PowerSeries.X ^ (first * left + second * right))) *
          (promote formalWeight * polynomialLift (poly left * poly right)) by
            simp only [pow_add, map_mul]; ring, hscalarTerm]
    change promoteQ _ * moment left right = _
    rw [horthogonal]
  have hfinite (cutoff : ℕ) :
      constantTerm (promote
        (formalWeight * (partialPolynomial first cutoff * partialPolynomial second cutoff))) =
        promoteQ (zeroth * partialScalar cutoff) := by
    simp only [partialPolynomial, map_mul, map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hsingle]
    simp only [mul_ite, mul_zero]
    rw [show (∑ left ∈ Finset.range cutoff, ∑ right ∈ Finset.range cutoff,
        if left = right then
          promoteQ (PowerSeries.X ^ (first * left + second * right)) * weightConstantTerm 1
        else 0) = ∑ left ∈ Finset.range cutoff,
          promoteQ (PowerSeries.X ^ ((first + second) * left)) * weightConstantTerm 1 by
            apply Finset.sum_congr rfl
            intro left hleft
            simp [hleft, add_mul]]
    simp only [partialScalar, map_sum, hzeroth, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring
  have hfiniteCoeff {R : Type} [CommRing R] (terms : ℕ → PowerSeries R)
      (hterms : ∀ index, (PowerSeries.X : PowerSeries R) ^ index ∣ terms index)
      (degree cutoff : ℕ) (hcutoff : degree < cutoff) :
      (∑ index ∈ Finset.range (degree + 1), PowerSeries.coeff degree (terms index)) =
        PowerSeries.coeff degree (∑ index ∈ Finset.range cutoff, terms index) := by
    rw [map_sum]
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro index _ hindex
    exact PowerSeries.X_pow_dvd_iff.mp (hterms index) degree (by
      have := Finset.mem_range.not.mp hindex
      omega)
  have hspecializationCoeff (power : ℕ) (hpower : 0 < power)
      (degree cutoff : ℕ) (hcutoff : degree < cutoff) :
      PowerSeries.coeff degree (polynomialSpecialization power) =
        PowerSeries.coeff degree (partialPolynomial power cutoff) := by
    have hterms (index : ℕ) :
        (PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)) ^ index ∣
          scalar (PowerSeries.X ^ (power * index)) * coefficients index := by
      have hbound : index ≤ power * index := by nlinarith
      refine ⟨PowerSeries.X ^ (power * index - index) * coefficients index, ?_⟩
      simp only [scalar, map_pow, PowerSeries.map_X, ← mul_assoc, ← pow_add,
        Nat.add_sub_of_le hbound]
    simpa only [polynomialSpecialization, PowerSeries.coeff_mk, partialPolynomial,
      scalar, map_pow, PowerSeries.map_X, coefficients, transpose] using
      hfiniteCoeff _ hterms degree cutoff hcutoff
  have hgeometricCoeff (degree cutoff : ℕ) (hcutoff : degree < cutoff) :
      PowerSeries.coeff degree geometric = PowerSeries.coeff degree (partialScalar cutoff) :=
    by
      simpa only [geometric, PowerSeries.coeff_mk, partialScalar] using
        hfiniteCoeff (fun index => (PowerSeries.X : PowerSeries ℚ) ^
            ((first + second) * index)) (fun index => by
      have hbound : index ≤ (first + second) * index := by nlinarith
      exact ⟨PowerSeries.X ^ ((first + second) * index - index), by
        rw [← pow_add, Nat.add_sub_of_le hbound]⟩) degree cutoff hcutoff
  have hproductCoeff {R : Type} [CommRing R] (left right leftPartial rightPartial :
      PowerSeries R) (degree : ℕ)
      (hleft : ∀ earlier ≤ degree,
        PowerSeries.coeff earlier left = PowerSeries.coeff earlier leftPartial)
      (hright : ∀ earlier ≤ degree,
        PowerSeries.coeff earlier right = PowerSeries.coeff earlier rightPartial) :
      PowerSeries.coeff degree (left * right) =
        PowerSeries.coeff degree (leftPartial * rightPartial) := by
    simp only [PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro pair hpair
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
    rw [hleft pair.1 (by omega), hright pair.2 (by omega)]
  have hmoment : constantTerm
      (promote (formalWeight * (polynomialSpecialization first *
        polynomialSpecialization second))) = promoteQ (zeroth * geometric) := by
    apply HahnSeries.ext
    funext degree
    change ((promote (formalWeight * (polynomialSpecialization first *
        polynomialSpecialization second))).coeff degree).coeff 0 =
      (promoteQ (zeroth * geometric)).coeff degree
    by_cases hnegative : degree < 0
    · simp only [promote, promoteQ, PowerSeries.coeff_coe, hnegative, ite_true]
      rfl
    · obtain ⟨count, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ degree)
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff]
      rw [hproductCoeff formalWeight _ formalWeight
          (partialPolynomial first (count + 1) * partialPolynomial second (count + 1)) count
          (fun _ _ => rfl)
          (fun earlier hearlier => hproductCoeff _ _ _ _ earlier
            (fun smaller hsmaller =>
              hspecializationCoeff first hfirst smaller (count + 1) (by omega))
            (fun smaller hsmaller =>
              hspecializationCoeff second hsecond smaller (count + 1) (by omega)))]
      rw [hproductCoeff zeroth _ zeroth (partialScalar (count + 1)) count
        (fun _ _ => rfl) (fun earlier hearlier =>
          hgeometricCoeff earlier (count + 1) (by omega))]
      have hequality := congrArg (fun series : LaurentSeries ℚ => series.coeff count)
        (hfinite (count + 1))
      change ((promote (formalWeight *
          (partialPolynomial first (count + 1) * partialPolynomial second (count + 1)))).coeff
            (count : ℤ)).coeff 0 =
        (promoteQ (zeroth * partialScalar (count + 1))).coeff (count : ℤ) at hequality
      simpa only [promote, promoteQ, HahnSeries.ofPowerSeries_apply_coeff] using hequality
  have htelescope (cutoff : ℕ) :
      (1 - (PowerSeries.X : PowerSeries ℚ) ^ (first + second)) * partialScalar cutoff =
        1 - PowerSeries.X ^ ((first + second) * cutoff) := by
    induction cutoff with
    | zero => simp [partialScalar]
    | succ cutoff ih =>
        rw [show partialScalar (cutoff + 1) = partialScalar cutoff +
            PowerSeries.X ^ ((first + second) * cutoff) by
              exact Finset.sum_range_succ _ cutoff,
          mul_add, ih, Nat.mul_add, Nat.mul_one, pow_add]
        ring
  have hgeometric : (1 - (PowerSeries.X : PowerSeries ℚ) ^ (first + second)) * geometric =
      1 := by
    apply PowerSeries.ext
    intro degree
    rw [hproductCoeff _ geometric _ (partialScalar (degree + 1)) degree
      (fun _ _ => rfl) (fun earlier hearlier =>
        hgeometricCoeff earlier (degree + 1) (by omega)), htelescope, map_sub]
    have hbound : degree < (first + second) * (degree + 1) := by nlinarith
    rw [PowerSeries.coeff_X_pow, if_neg (by omega), sub_zero]
  change (1 - promoteQ PowerSeries.X ^ (first + second)) * constantTerm
    (promote formalWeight *
      (promote (polynomialSpecialization first) * promote (polynomialSpecialization second))) =
        weightConstantTerm 1
  rw [← map_mul, ← map_mul, hmoment, hzeroth]
  calc
    _ = promoteQ (zeroth * ((1 - PowerSeries.X ^ (first + second)) * geometric)) := by
      simp only [map_mul, map_sub, map_one, map_pow]
      ring
    _ = promoteQ zeroth := by rw [hgeometric, mul_one]

end D5.S3.Combinatorics.InversionSeq.InversionSeq207Orthogonality
