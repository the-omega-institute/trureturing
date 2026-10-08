/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207Resolvent
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207Resolvent
   mirror-E: none(waiver:locally-finite-formal-resolvent)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Trunc]
   utility: none
   digest: Valuation bounds and boundary cancellation construct the polynomial resolvent. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207Eigen
import D5.S3.Combinatorics.InversionSeq.InversionSeq207Tridiagonal
import Mathlib.RingTheory.PowerSeries.Trunc

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207Resolvent

open InversionSeq207Polynomials InversionSeq207Tridiagonal

noncomputable def polynomialSpecialization (power : ℕ) :
    PowerSeries (LaurentPolynomial ℚ) :=
  let transpose : LaurentPolynomial (PowerSeries ℚ) →+*
      PowerSeries (LaurentPolynomial ℚ) :=
    LaurentPolynomial.eval₂ (PowerSeries.map LaurentPolynomial.C)
    (Units.map PowerSeries.C.toMonoidHom (unitOfInvertible (LaurentPolynomial.T 1)))
  PowerSeries.mk fun degree =>
    ∑ index ∈ Finset.range (degree + 1), PowerSeries.coeff degree
      (PowerSeries.X ^ (power * index) *
        transpose (PowerSeries.coeff index polynomialGenerator))

noncomputable def tridiagonalResolvent : PowerSeries (LaurentPolynomial ℚ) :=
  let transpose : LaurentPolynomial (PowerSeries ℚ) →+*
      PowerSeries (LaurentPolynomial ℚ) :=
    LaurentPolynomial.eval₂ (PowerSeries.map LaurentPolynomial.C)
    (Units.map PowerSeries.C.toMonoidHom (unitOfInvertible (LaurentPolynomial.T 1)))
  let weights := fun index => PowerSeries.mk fun degree =>
    PowerSeries.coeff (degree + index)
      (PowerSeries.expand 2 (by decide) (tridiagonalSeries index))
  PowerSeries.mk fun degree =>
    ∑ index ∈ Finset.range (degree + 1), PowerSeries.coeff degree
      (PowerSeries.map LaurentPolynomial.C (weights index) *
        transpose (PowerSeries.coeff index polynomialGenerator))

set_option maxHeartbeats 1800000 in
theorem tridiagonal_resolvent :
    (1 - 2 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 4 + PowerSeries.X ^ 6 +
        PowerSeries.X ^ 3 * PowerSeries.C
          (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1))) * tridiagonalResolvent =
      (1 - PowerSeries.X ^ 4) ^ 2 * polynomialSpecialization 3 := by
  classical
  let expand := (PowerSeries.expand 2 (by decide) :
    PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ).toRingHom
  let weights := fun index => PowerSeries.mk fun degree =>
    PowerSeries.coeff (degree + index) (expand (tridiagonalSeries index))
  let transpose : LaurentPolynomial (PowerSeries ℚ) →+*
      PowerSeries (LaurentPolynomial ℚ) :=
    LaurentPolynomial.eval₂ (PowerSeries.map LaurentPolynomial.C)
    (Units.map PowerSeries.C.toMonoidHom (unitOfInvertible (LaurentPolynomial.T 1)))
  let scalar := (PowerSeries.map LaurentPolynomial.C :
    PowerSeries ℚ →+* PowerSeries (LaurentPolynomial ℚ))
  let poly := fun index => transpose (PowerSeries.coeff index polynomialGenerator)
  let weight := fun index => scalar (weights index)
  let rho : PowerSeries (LaurentPolynomial ℚ) := PowerSeries.X
  let slope : PowerSeries (LaurentPolynomial ℚ) :=
    PowerSeries.C (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1))
  let diagonal := fun index =>
    1 - 2 * rho ^ 2 - 2 * rho ^ 4 + rho ^ 6 + 2 * rho ^ (2 * index + 4)
  let adjacent := fun index => rho ^ 3 * (1 - rho ^ (2 * index))
  let kernel := 1 - 2 * rho ^ 2 - 2 * rho ^ 4 + rho ^ 6 + rho ^ 3 * slope
  let forcing := (1 - rho ^ 4) ^ 2
  have hexpandDiv (index : ℕ) :
      (PowerSeries.X : PowerSeries ℚ) ^ (2 * index) ∣
        expand (tridiagonalSeries index) := by
    obtain ⟨quotient, hequality⟩ := tridiagonal_solution.1 index
    refine ⟨expand quotient, ?_⟩
    rw [hequality, map_mul, map_pow]
    simp [expand, pow_mul]
  have hshift (index : ℕ) : expand (tridiagonalSeries index) =
      PowerSeries.X ^ index * weights index := by
    apply PowerSeries.ext
    intro degree
    rw [PowerSeries.coeff_X_pow_mul']
    split_ifs with hle
    · simp [weights, Nat.sub_add_cancel hle]
    · exact ((PowerSeries.X_pow_dvd_iff).mp (hexpandDiv index)) degree (by omega)
  have hweightDiv (index : ℕ) :
      (PowerSeries.X : PowerSeries ℚ) ^ index ∣ weights index := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro degree hdegree
    simpa only [weights, PowerSeries.coeff_mk] using
      ((PowerSeries.X_pow_dvd_iff).mp (hexpandDiv index))
      (degree + index) (by omega)
  have hscalarX : scalar PowerSeries.X = rho := by simp [scalar, rho]
  have hweights (index : ℕ) : rho ^ index ∣ weight index := by
    obtain ⟨quotient, hequality⟩ := hweightDiv index
    exact ⟨scalar quotient, by simp [weight, hequality, hscalarX]⟩
  have hrow (index : ℕ) :
      adjacent (index + 1) * weight (index + 1) + diagonal index * weight index +
        adjacent index * weight (index - 1) = forcing * rho ^ (3 * index) := by
    have hequality := congrArg expand (tridiagonal_solution.2.1 index)
    have hX : expand PowerSeries.X = (PowerSeries.X : PowerSeries ℚ) ^ 2 := by
      simp [expand]
    simp only [map_add, map_sub, map_neg, map_mul, map_pow, map_one, map_ofNat,
      tridiagonalRow, hX, ← pow_mul] at hequality
    have hrecurrence :
        (PowerSeries.X : PowerSeries ℚ) ^ 3 * (1 - PowerSeries.X ^ (2 * (index + 1))) *
            weights (index + 1) +
          (1 - 2 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 4 + PowerSeries.X ^ 6 +
            2 * PowerSeries.X ^ (2 * index + 4)) * weights index +
          PowerSeries.X ^ 3 * (1 - PowerSeries.X ^ (2 * index)) * weights (index - 1) =
            (1 - PowerSeries.X ^ 4) ^ 2 * PowerSeries.X ^ (3 * index) := by
      apply mul_left_cancel₀ (pow_ne_zero index PowerSeries.X_ne_zero)
      rw [hshift index, hshift (index + 1), hshift (index - 1)] at hequality
      by_cases hzero : index = 0
      · subst index
        simp only [Nat.zero_add, Nat.zero_sub, pow_zero, sub_self,
          zero_mul, mul_zero, add_zero, mul_one, one_mul] at hequality ⊢
        convert hequality using 1; ring
      · have hprevious : PowerSeries.X ^ (index + 3) =
            (PowerSeries.X : PowerSeries ℚ) ^ 4 * PowerSeries.X ^ (index - 1) := by
          rw [← pow_add]
          congr 1
          omega
        have hnext : PowerSeries.X ^ (index + 3) =
            (PowerSeries.X : PowerSeries ℚ) ^ 2 * PowerSeries.X ^ (index + 1) := by
          rw [← pow_add]
          congr 1
          omega
        have hdiagonal : PowerSeries.X ^ (2 * (index + 2)) =
            (PowerSeries.X : PowerSeries ℚ) ^ (2 * index + 4) := by congr 1
        have hfirst : PowerSeries.X ^ index *
            (PowerSeries.X : PowerSeries ℚ) ^ 3 = PowerSeries.X ^ (index + 3) := by
          rw [pow_add]
        rw [mul_add, mul_add]
        simp only [← mul_assoc, hfirst]
        rw [show PowerSeries.X ^ (index + 3) *
            (1 - (PowerSeries.X : PowerSeries ℚ) ^ (2 * (index + 1))) *
              weights (index + 1) =
            PowerSeries.X ^ 2 * (1 - PowerSeries.X ^ (2 * (index + 1))) *
              (PowerSeries.X ^ (index + 1) * weights (index + 1)) by
                rw [hnext]; ring]
        rw [show PowerSeries.X ^ (index + 3) *
            (1 - (PowerSeries.X : PowerSeries ℚ) ^ (2 * index)) * weights (index - 1) =
            PowerSeries.X ^ 4 * (1 - PowerSeries.X ^ (2 * index)) *
              (PowerSeries.X ^ (index - 1) * weights (index - 1)) by
                rw [hprevious]; ring]
        rw [hdiagonal] at hequality
        convert hequality using 1 <;> ring
    have htransfer := congrArg scalar hrecurrence
    simpa [scalar, weight, rho, adjacent, diagonal, forcing, map_add, map_sub,
      map_mul, map_pow, map_one, map_ofNat] using htransfer
  have htransposeC (value : PowerSeries ℚ) :
      transpose (LaurentPolynomial.C value) = scalar value := by
    simp [transpose, scalar]
  have htransposeT (location : ℤ) :
      transpose (LaurentPolynomial.T location) =
        PowerSeries.C (LaurentPolynomial.T location) := by
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
    simp only [transpose, LaurentPolynomial.eval₂_T, ← map_zpow, Units.coe_map, hunit]
    rfl
  have hpoly (index : ℕ) :
      kernel * poly index = diagonal index * poly index +
        adjacent (index + 1) * poly (index + 1) + adjacent index * poly (index - 1) := by
    have hequality := congrArg transpose (polynomial_system.{0}.2.1 index)
    simp only [map_mul, map_sub, map_add, map_one, map_ofNat, htransposeC,
      htransposeT, map_pow, hscalarX] at hequality
    rw [← map_add PowerSeries.C] at hequality
    change (1 - rho ^ (2 * (index + 1))) * poly (index + 1) =
      (slope - 2 * rho ^ (2 * index + 1)) * poly index -
        (1 - rho ^ (2 * index)) * transpose
          (if index = 0 then 0 else PowerSeries.coeff (index - 1) polynomialGenerator)
      at hequality
    have hprevious : (1 - rho ^ (2 * index)) * transpose
        (if index = 0 then 0 else PowerSeries.coeff (index - 1) polynomialGenerator) =
          (1 - rho ^ (2 * index)) * poly (index - 1) := by
      split_ifs with hzero
      · subst index; simp
      · rfl
    rw [hprevious] at hequality
    have hmultiplied := congrArg (fun value => rho ^ 3 * value) hequality
    dsimp [kernel, diagonal, adjacent]
    linear_combination -hmultiplied
  let partialSum := fun cutoff => ∑ index ∈ Finset.range cutoff, weight index * poly index
  let generator := fun cutoff =>
    ∑ index ∈ Finset.range cutoff, rho ^ (3 * index) * poly index
  have hboundary (cutoff : ℕ) : kernel * partialSum cutoff = forcing * generator cutoff +
      adjacent cutoff * (weight (cutoff - 1) * poly cutoff -
        weight cutoff * poly (cutoff - 1)) := by
    induction cutoff with
    | zero => simp [partialSum, generator, adjacent]
    | succ cutoff ih =>
        simp only [partialSum, generator, Finset.sum_range_succ] at ih ⊢
        rw [mul_add, ih, Nat.add_sub_cancel]
        have hleft := congrArg (fun value => value * poly cutoff) (hrow cutoff)
        have hright := congrArg (fun value => weight cutoff * value) (hpoly cutoff)
        linear_combination hright + hleft
  have htermDiv (index : ℕ) : rho ^ index ∣ weight index * poly index :=
    dvd_mul_of_dvd_left (hweights index) _
  have hgeneratorDiv (index : ℕ) : rho ^ index ∣ rho ^ (3 * index) * poly index := by
    apply dvd_mul_of_dvd_left
    exact pow_dvd_pow rho (by omega : index ≤ 3 * index)
  have hfiniteCoeff (terms : ℕ → PowerSeries (LaurentPolynomial ℚ))
      (hterms : ∀ index, rho ^ index ∣ terms index) (degree cutoff : ℕ)
      (hcutoff : degree < cutoff) :
      (∑ index ∈ Finset.range (degree + 1), PowerSeries.coeff degree (terms index)) =
        PowerSeries.coeff degree (∑ index ∈ Finset.range cutoff, terms index) := by
    rw [map_sum]
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro index _ hindex
    exact PowerSeries.X_pow_dvd_iff.mp (hterms index) degree (by
      have := (Finset.mem_range.not.mp hindex)
      omega)
  have hpartialCoeff (degree cutoff : ℕ) (hcutoff : degree < cutoff) :
      PowerSeries.coeff degree tridiagonalResolvent =
        PowerSeries.coeff degree (partialSum cutoff) := by
    simpa only [tridiagonalResolvent, PowerSeries.coeff_mk, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom,
      weight, scalar, weights,
      expand, poly, transpose, partialSum] using
      hfiniteCoeff (fun index => weight index * poly index) htermDiv degree cutoff hcutoff
  have hgeneratorCoeff (degree cutoff : ℕ) (hcutoff : degree < cutoff) :
      PowerSeries.coeff degree (polynomialSpecialization 3) =
        PowerSeries.coeff degree (generator cutoff) := by
    simpa only [polynomialSpecialization, PowerSeries.coeff_mk] using
      hfiniteCoeff (fun index => rho ^ (3 * index) * poly index) hgeneratorDiv
        degree cutoff hcutoff
  have hproductCoeff (factor left right : PowerSeries (LaurentPolynomial ℚ))
      (degree : ℕ) (hagrees : ∀ earlier ≤ degree,
        PowerSeries.coeff earlier left = PowerSeries.coeff earlier right) :
      PowerSeries.coeff degree (factor * left) = PowerSeries.coeff degree (factor * right) := by
    simp only [PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro split hsplit
    rw [hagrees split.2 (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hsplit; omega)]
  change kernel * tridiagonalResolvent = forcing * polynomialSpecialization 3
  apply PowerSeries.ext
  intro degree
  rw [hproductCoeff kernel _ (partialSum (degree + 2)) degree
    (fun earlier hearlier => hpartialCoeff earlier (degree + 2) (by omega)), hboundary]
  rw [map_add, hproductCoeff forcing (polynomialSpecialization 3)
    (generator (degree + 2)) degree
      (fun earlier hearlier => hgeneratorCoeff earlier (degree + 2) (by omega))]
  have hvanishes : rho ^ (degree + 1) ∣
      adjacent (degree + 2) * (weight (degree + 2 - 1) * poly (degree + 2) -
        weight (degree + 2) * poly (degree + 2 - 1)) := by
    apply dvd_mul_of_dvd_right
    apply dvd_sub
    · exact dvd_mul_of_dvd_left (by simpa using hweights (degree + 1)) _
    · exact dvd_mul_of_dvd_left
        ((pow_dvd_pow rho (by omega : degree + 1 ≤ degree + 2)).trans
          (hweights (degree + 2))) _
  rw [PowerSeries.X_pow_dvd_iff.mp hvanishes degree (by omega), add_zero]

end D5.S3.Combinatorics.InversionSeq.InversionSeq207Resolvent
