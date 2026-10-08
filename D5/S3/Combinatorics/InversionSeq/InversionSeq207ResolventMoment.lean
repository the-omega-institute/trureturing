/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207ResolventMoment
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207ResolventMoment
   mirror-E: none(waiver:locally-finite-root-contraction)
   anchors: []
   utility: none
   digest: Finite orthogonal contractions and valuation cutoffs identify the right root moment. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207Resolvent
import D5.S3.Combinatorics.InversionSeq.InversionSeq207Orthogonality
import D5.S3.Combinatorics.InversionSeq.InversionSeq207NormalizationDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207ResolventMoment

open InversionSeq207Resolvent InversionSeq207Polynomials InversionSeq207Tridiagonal
open InversionSeq207SelfAdjoint InversionSeq207Orthogonality InversionSeq207Pearson
open InversionSeq207Normalization

set_option maxHeartbeats 1800000 in
theorem tridiagonal_root_moment :
    let rho : LaurentSeries ℚ := (PowerSeries.X : PowerSeries ℚ)
    (1 - rho ^ 2) * constantTerm
        ((formalWeight : LaurentSeries (LaurentPolynomial ℚ)) *
          ((polynomialSpecialization 1 : LaurentSeries (LaurentPolynomial ℚ)) *
            (tridiagonalResolvent : LaurentSeries (LaurentPolynomial ℚ)))) =
      weightConstantTerm 1 *
        ((PowerSeries.expand 2 (by decide) rightScalarSeries : PowerSeries ℚ) :
          LaurentSeries ℚ) := by
  classical
  let promote := HahnSeries.ofPowerSeries ℤ (LaurentPolynomial ℚ)
  let promoteQ := HahnSeries.ofPowerSeries ℤ ℚ
  let scalar := (PowerSeries.map LaurentPolynomial.C :
    PowerSeries ℚ →+* PowerSeries (LaurentPolynomial ℚ))
  let transfer := AddMonoidAlgebra.mapRingHom ℤ promoteQ
  let transpose : LaurentPolynomial (PowerSeries ℚ) →+*
      PowerSeries (LaurentPolynomial ℚ) :=
    LaurentPolynomial.eval₂ scalar
      (Units.map PowerSeries.C.toMonoidHom (unitOfInvertible (LaurentPolynomial.T 1)))
  let poly := fun index => transpose (PowerSeries.coeff index polynomialGenerator)
  let weights := fun index => PowerSeries.mk fun degree =>
    PowerSeries.coeff (degree + index)
      (PowerSeries.expand 2 (by decide) (tridiagonalSeries index))
  let partialFirst := fun cutoff =>
    ∑ index ∈ Finset.range cutoff, scalar (PowerSeries.X ^ index) * poly index
  let partialSecond := fun cutoff =>
    ∑ index ∈ Finset.range cutoff, scalar (weights index) * poly index
  let partialScalar := fun cutoff =>
    ∑ index ∈ Finset.range cutoff, PowerSeries.X ^ index * weights index
  let zeroth := PowerSeries.mk fun degree =>
    (PowerSeries.coeff degree formalWeight).coeff 0
  let originalSum := PowerSeries.mk fun degree =>
    ∑ index ∈ Finset.range (degree + 1), PowerSeries.coeff degree (tridiagonalSeries index)
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
        (LaurentPolynomial ℚ)ˣ) : LaurentPolynomial ℚ) =
          LaurentPolynomial.T location := by
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
        transpose (LaurentPolynomial.C value) = scalar value := by
      simp [transpose]
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
    | h_C value =>
        rw [htransposeC, htransferC, hliftC, hscalar]
    | h_add hleft hright => simp only [map_add, hleft, hright]
    | h_C_mul_T index value _ =>
        simp only [map_mul, htransferC, htransferT, htransposeC, htransposeT,
          hliftC, hliftT, hscalar]
        rw [HahnSeries.ofPowerSeries_C]
    | h_C_mul_T_Z index value _ =>
        simp only [map_mul, htransferC, htransferT, htransposeC, htransposeT,
          hliftC, hliftT, hscalar]
        rw [HahnSeries.ofPowerSeries_C]
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
  have hzeroth : weightConstantTerm 1 = promoteQ zeroth := by
    apply HahnSeries.ext
    funext degree
    by_cases hnegative : degree < 0
    · simp [weightConstantTerm, constantTerm, HahnSeries.map_coeff, promoteQ,
        PowerSeries.coeff_coe, hnegative]
    · obtain ⟨count, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ degree)
      simp [weightConstantTerm, constantTerm, HahnSeries.map_coeff, promoteQ,
        zeroth]
  have hsingle (first second : ℕ) (left right : PowerSeries ℚ) :
      constantTerm (promote formalWeight *
        (promote (scalar left) * promote (poly first) *
          (promote (scalar right) * promote (poly second)))) =
          promoteQ (left * right) *
            (if first = second then weightConstantTerm 1 else 0) := by
    simp only [map_mul, hscalar, poly, htranspose]
    rw [show promote formalWeight *
        (coefficientLift (promoteQ left) *
          polynomialLift (transfer (PowerSeries.coeff first polynomialGenerator)) *
          (coefficientLift (promoteQ right) *
            polynomialLift (transfer (PowerSeries.coeff second polynomialGenerator)))) =
        coefficientLift (promoteQ (left * right)) *
          (promote formalWeight * polynomialLift
            (transfer (PowerSeries.coeff first polynomialGenerator) *
              transfer (PowerSeries.coeff second polynomialGenerator))) by
                simp only [map_mul]; ring, hscalarTerm]
    change promoteQ (left * right) * weightConstantTerm
      (transfer (PowerSeries.coeff first polynomialGenerator) *
        transfer (PowerSeries.coeff second polynomialGenerator)) = _
    rw [(polynomial_orthogonality first second).1]
    rw [map_mul]
  have hfinite (cutoff : ℕ) :
      constantTerm (promote (formalWeight * (partialFirst cutoff * partialSecond cutoff))) =
        promoteQ (zeroth * partialScalar cutoff) := by
    simp only [partialFirst, partialSecond, map_mul, map_sum, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hsingle]
    simp only [mul_ite, mul_zero]
    rw [show (∑ first ∈ Finset.range cutoff,
        ∑ second ∈ Finset.range cutoff,
          if first = second then
            promoteQ (PowerSeries.X ^ first * weights second) * weightConstantTerm 1
          else 0) =
        ∑ first ∈ Finset.range cutoff,
          promoteQ (PowerSeries.X ^ first * weights first) * weightConstantTerm 1 by
            apply Finset.sum_congr rfl
            intro first hfirst
            simp [hfirst]]
    simp only [partialScalar, map_mul, map_sum, hzeroth, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring
  have hdiv (index : ℕ) : (PowerSeries.X : PowerSeries ℚ) ^ (2 * index) ∣
      PowerSeries.expand 2 (by decide) (tridiagonalSeries index) := by
    obtain ⟨quotient, hequality⟩ := tridiagonal_solution.1 index
    refine ⟨PowerSeries.expand 2 (by decide) quotient, ?_⟩
    simp [hequality, pow_mul]
  have hshift (index : ℕ) : PowerSeries.expand 2 (by decide) (tridiagonalSeries index) =
      PowerSeries.X ^ index * weights index := by
    apply PowerSeries.ext
    intro degree
    rw [PowerSeries.coeff_X_pow_mul']
    split_ifs with hle
    · simp [weights, Nat.sub_add_cancel hle]
    · exact PowerSeries.X_pow_dvd_iff.mp (hdiv index) degree (by omega)
  have hweights (index : ℕ) : (PowerSeries.X : PowerSeries ℚ) ^ index ∣ weights index := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro degree hdegree
    simpa only [weights, PowerSeries.coeff_mk] using
      PowerSeries.X_pow_dvd_iff.mp (hdiv index) (degree + index) (by omega)
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
  have hfirstCoeff (degree cutoff : ℕ) (hcutoff : degree < cutoff) :
      PowerSeries.coeff degree (polynomialSpecialization 1) =
        PowerSeries.coeff degree (partialFirst cutoff) := by
    simpa only [polynomialSpecialization, PowerSeries.coeff_mk, one_mul,
      partialFirst, scalar, map_pow, PowerSeries.map_X] using
      hfiniteCoeff (fun index => PowerSeries.X ^ index * poly index)
        (fun index => dvd_mul_right _ _) degree cutoff hcutoff
  have hsecondCoeff (degree cutoff : ℕ) (hcutoff : degree < cutoff) :
      PowerSeries.coeff degree tridiagonalResolvent =
        PowerSeries.coeff degree (partialSecond cutoff) := by
    have hterms (index : ℕ) : (PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)) ^ index ∣
        scalar (weights index) * poly index := by
      obtain ⟨quotient, hequality⟩ := hweights index
      refine ⟨scalar quotient * poly index, ?_⟩
      simp [hequality, scalar, mul_assoc]
    simpa only [tridiagonalResolvent, PowerSeries.coeff_mk] using
      hfiniteCoeff (fun index => scalar (weights index) * poly index)
        hterms degree cutoff hcutoff
  have hscalarCoeff (degree cutoff : ℕ) (hcutoff : degree < cutoff) :
      PowerSeries.coeff degree (PowerSeries.expand 2 (by decide) originalSum) =
        PowerSeries.coeff degree (partialScalar cutoff) := by
    dsimp only [partialScalar]
    simp_rw [← hshift]
    rw [map_sum]
    simp only [PowerSeries.coeff_expand]
    by_cases hparity : 2 ∣ degree
    · simp only [hparity, if_true, originalSum, PowerSeries.coeff_mk]
      simpa only [map_sum] using hfiniteCoeff tridiagonalSeries tridiagonal_solution.1
        (degree / 2) cutoff (by omega)
    · simp [hparity]
  have hproductCoeff {R : Type} [CommRing R] (first second third fourth : PowerSeries R)
      (degree : ℕ) (hfirst : ∀ earlier ≤ degree,
        PowerSeries.coeff earlier first = PowerSeries.coeff earlier third)
      (hsecond : ∀ earlier ≤ degree,
        PowerSeries.coeff earlier second = PowerSeries.coeff earlier fourth) :
      PowerSeries.coeff degree (first * second) =
        PowerSeries.coeff degree (third * fourth) := by
    simp only [PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro split hsplit
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hsplit
    rw [hfirst split.1 (by omega), hsecond split.2 (by omega)]
  have hmoment : constantTerm (promote
      (formalWeight * (polynomialSpecialization 1 * tridiagonalResolvent))) =
        promoteQ (zeroth * PowerSeries.expand 2 (by decide) originalSum) := by
    apply HahnSeries.ext
    funext degree
    by_cases hnegative : degree < 0
    · change ((promote
          (formalWeight * (polynomialSpecialization 1 * tridiagonalResolvent))).coeff
            degree).coeff 0 =
        (promoteQ (zeroth * PowerSeries.expand 2 (by decide) originalSum)).coeff degree
      simp only [promote, promoteQ, PowerSeries.coeff_coe, hnegative, ite_true]
      rfl
    · obtain ⟨count, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ degree)
      change ((promote
          (formalWeight * (polynomialSpecialization 1 * tridiagonalResolvent))).coeff
            (count : ℤ)).coeff 0 =
        (promoteQ (zeroth * PowerSeries.expand 2 (by decide) originalSum)).coeff (count : ℤ)
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff]
      rw [hproductCoeff formalWeight _ formalWeight
          (partialFirst (count + 1) * partialSecond (count + 1)) count (fun _ _ => rfl)
          (fun earlier hearlier => hproductCoeff _ _ _ _ earlier
            (fun smaller hsmaller => hfirstCoeff smaller (count + 1) (by omega))
            (fun smaller hsmaller => hsecondCoeff smaller (count + 1) (by omega)))]
      rw [hproductCoeff zeroth _ zeroth (partialScalar (count + 1)) count (fun _ _ => rfl)
        (fun earlier hearlier => hscalarCoeff earlier (count + 1) (by omega))]
      have hequality := congrArg (fun series : LaurentSeries ℚ => series.coeff count)
        (hfinite (count + 1))
      change ((promote (formalWeight *
          (partialFirst (count + 1) * partialSecond (count + 1)))).coeff
            (count : ℤ)).coeff 0 =
        (promoteQ (zeroth * partialScalar (count + 1))).coeff (count : ℤ) at hequality
      simpa only [promote, promoteQ, HahnSeries.ofPowerSeries_apply_coeff] using hequality
  have hright : rightScalarSeries = (1 - PowerSeries.X) * originalSum := rfl
  change (1 - promoteQ PowerSeries.X ^ 2) * constantTerm
      (promote formalWeight *
        (promote (polynomialSpecialization 1) * promote tridiagonalResolvent)) =
    weightConstantTerm 1 * promoteQ (PowerSeries.expand 2 (by decide) rightScalarSeries)
  rw [← map_mul, ← map_mul, hmoment, hzeroth, hright]
  simp only [map_mul, map_sub, map_one, PowerSeries.expand_X, map_pow]
  ring

end D5.S3.Combinatorics.InversionSeq.InversionSeq207ResolventMoment
