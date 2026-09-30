/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoKernel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoKernel
   mirror-E: none(waiver:formal-catalytic-kernel)
   anchors: [mathlib/module/Mathlib]
   utility: none
   digest: Constructs the catalytic kernel and extracts the all-degree counting recurrence. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoKernel

open PowerSeries
open scoped PowerSeries.WithPiTopology

theorem catalytic_recurrence (series : PowerSeries ℚ)
    (constant : constantCoeff series = 1) (bivariate : PowerSeries (Polynomial ℚ))
    (equation :
      let lifted := series.map Polynomial.C
      let catalan := rescale Polynomial.X
        ((catalanSeries.map (Nat.castRingHom ℚ)).map Polynomial.C)
      let marker : PowerSeries (Polynomial ℚ) := C Polynomial.X
      (1 - marker + X * marker ^ 2 * (lifted + catalan)) * bivariate =
        1 - marker + X * marker * lifted ^ 2 + X * marker ^ 2 * catalan * lifted) :
    ∀ degree : ℕ, 1 ≤ degree →
      coeff degree series =
        (∑ index ∈ Finset.Icc 1 (degree - 1),
          coeff index series * coeff (degree - index) series) +
        ∑ outer ∈ Finset.HasAntidiagonal.antidiagonal (degree - 1),
          ∑ inner ∈ Finset.HasAntidiagonal.antidiagonal outer.1,
            coeff inner.1 series * coeff inner.2 series * coeff outer.2 series := by
  classical
  have productPrefix (degree : ℕ) (left right left' right' : PowerSeries ℚ)
      (leftEqual : ∀ index ≤ degree, coeff index left = coeff index left')
      (rightEqual : ∀ index ≤ degree, coeff index right = coeff index right') :
      coeff degree (left * right) = coeff degree (left' * right') := by
    rw [coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro indices member
    have total := Finset.HasAntidiagonal.mem_antidiagonal.mp member
    rw [leftEqual indices.1 (by omega), rightEqual indices.2 (by omega)]
  have kernelPrefix (degree : ℕ) (upper lower upper' lower' : PowerSeries ℚ)
      (upperEqual : ∀ index ≤ degree, coeff index upper = coeff index upper')
      (lowerEqual : ∀ index ≤ degree, coeff index lower = coeff index lower') :
      coeff degree (upper ^ 2 * (series + lower)) =
          coeff degree (upper' ^ 2 * (series + lower')) ∧
        coeff degree (upper * lower ^ 2) = coeff degree (upper' * lower' ^ 2) := by
    have squares (left right : PowerSeries ℚ)
        (equal : ∀ index ≤ degree, coeff index left = coeff index right) :
        ∀ index ≤ degree, coeff index (left ^ 2) = coeff index (right ^ 2) := by
      intro index bound
      simpa only [pow_two] using productPrefix index left left right right
        (fun smaller smallerBound => equal smaller (by omega))
        (fun smaller smallerBound => equal smaller (by omega))
    constructor
    · apply productPrefix degree (upper ^ 2) (series + lower)
        (upper' ^ 2) (series + lower') (squares upper upper' upperEqual)
      intro index bound
      simp only [map_add, lowerEqual index bound]
    · exact productPrefix degree upper (lower ^ 2) upper' (lower' ^ 2)
        upperEqual (squares lower lower' lowerEqual)
  let step (degree : ℕ) (previous : ∀ index < degree, ℚ × ℚ) : ℚ × ℚ :=
    if degree = 0 then (1, 1) else
      let upper := mk fun index => if bound : index < degree then
        (previous index bound).1 else 0
      let lower := mk fun index => if bound : index < degree then
        (previous index bound).2 else 0
      (coeff (degree - 1) (upper ^ 2 * (series + lower)),
        coeff (degree - 1) (upper * lower ^ 2))
  let coefficients : ℕ → ℚ × ℚ := Nat.strongRec step
  let upper : PowerSeries ℚ := mk fun index => (coefficients index).1
  let lower : PowerSeries ℚ := mk fun index => (coefficients index).2
  have coefficientEquation (degree : ℕ) :
      coefficients degree = step degree (fun index _ => coefficients index) := by
    exact Nat.strongRec_eq step degree
  have initial : coefficients 0 = (1, 1) := by
    rw [coefficientEquation]
    simp [step]
  have successors (degree : ℕ) :
      coefficients (degree + 1) =
        (coeff degree (upper ^ 2 * (series + lower)),
          coeff degree (upper * lower ^ 2)) := by
    rw [coefficientEquation]
    simp only [step, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel]
    have upperPrefix : ∀ index ≤ degree,
        coeff index (mk fun index => if bound : index < degree + 1 then
          (coefficients index).1 else 0) = coeff index upper := by
      intro index bound
      simp only [coeff_mk, dif_pos (show index < degree + 1 by omega), upper]
    have lowerPrefix : ∀ index ≤ degree,
        coeff index (mk fun index => if bound : index < degree + 1 then
          (coefficients index).2 else 0) = coeff index lower := by
      intro index bound
      simp only [coeff_mk, dif_pos (show index < degree + 1 by omega), lower]
    exact Prod.ext (kernelPrefix degree _ _ upper lower upperPrefix lowerPrefix).1
      (kernelPrefix degree _ _ upper lower upperPrefix lowerPrefix).2
  have upperEquation : upper = 1 + X * upper ^ 2 * (series + lower) := by
    ext degree
    cases degree with
    | zero => simp [upper, initial]
    | succ degree =>
      have value := congrArg Prod.fst (successors degree)
      simpa [upper, coeff_succ_X_mul, mul_assoc] using value
  have lowerEquation : lower = 1 + X * upper * lower ^ 2 := by
    ext degree
    cases degree with
    | zero => simp [lower, initial]
    | succ degree =>
      have value := congrArg Prod.snd (successors degree)
      simpa [lower, coeff_succ_X_mul, mul_assoc] using value
  let : UniformSpace ℚ := ⊥
  let : UniformSpace (Polynomial ℚ) := ⊥
  let coefficientEvaluation := Polynomial.eval₂RingHom (C : ℚ →+* PowerSeries ℚ) upper
  have continuousCoefficient : Continuous coefficientEvaluation := continuous_of_discreteTopology
  let evaluation := eval₂Hom continuousCoefficient (HasEval.X (R := ℚ))
  have evaluateX : evaluation X = X := by
    simp [evaluation, coe_eval₂Hom]
  have evaluateVariable : evaluation (C Polynomial.X) = upper := by
    simp [evaluation, coe_eval₂Hom, coefficientEvaluation, Polynomial.coe_eval₂RingHom]
  have evaluateLifted (source : PowerSeries ℚ) :
      evaluation (source.map Polynomial.C) = source := by
    have evaluated := hasSum_eval₂ continuousCoefficient (HasEval.X (R := ℚ))
      (source.map Polynomial.C)
    have ordinary := hasSum_of_monomials_self source
    have sameTerms : (fun index => coefficientEvaluation
        (coeff index (source.map Polynomial.C)) * X ^ index) =
        (fun index => monomial index (coeff index source)) := by
      funext index
      simp [coefficientEvaluation, coeff_map, Polynomial.coe_eval₂RingHom,
        monomial_eq_C_mul_X_pow]
    rw [sameTerms] at evaluated
    simpa only [evaluation, coe_eval₂Hom] using evaluated.unique ordinary
  let catalan : PowerSeries ℚ := catalanSeries.map (Nat.castRingHom ℚ)
  let scaled : PowerSeries (Polynomial ℚ) :=
    rescale Polynomial.X (catalan.map Polynomial.C)
  have catalanEquation : catalan = 1 + X * catalan ^ 2 := by
    have mapped := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      catalanSeries_sq_mul_X_add_one
    simpa [catalan, mul_comm, add_comm] using mapped.symm
  have scaledEquation : scaled = 1 + X * C Polynomial.X * scaled ^ 2 := by
    have mapped := congrArg
      (fun source : PowerSeries ℚ => rescale Polynomial.X (source.map Polynomial.C))
      catalanEquation
    simpa [scaled, map_mul, map_pow, map_add, rescale_X, mul_comm, mul_left_comm,
      mul_assoc] using mapped
  have imageEquation : evaluation scaled = 1 + X * upper * (evaluation scaled) ^ 2 := by
    have mapped := congrArg evaluation scaledEquation
    simpa only [map_add, map_one, map_mul, map_pow, evaluateX, evaluateVariable] using mapped
  have imageLower : evaluation scaled = lower := by
    have difference : (evaluation scaled - lower) *
        (1 - X * upper * (evaluation scaled + lower)) = 0 := by
      linear_combination imageEquation - lowerEquation
    have factorNonzero : 1 - X * upper * (evaluation scaled + lower) ≠ 0 := by
      intro zero
      have value := congrArg constantCoeff zero
      simp at value
    exact sub_eq_zero.mp ((mul_eq_zero.mp difference).resolve_right factorNonzero)
  have evaluated : (1 - upper + X * upper ^ 2 * (series + lower)) *
      evaluation bivariate =
        1 - upper + X * upper * series ^ 2 + X * upper ^ 2 * lower * series := by
    have mapped := congrArg evaluation equation
    change evaluation ((1 - C Polynomial.X + X * C Polynomial.X ^ 2 *
      (series.map Polynomial.C + scaled)) * bivariate) =
      evaluation (1 - C Polynomial.X + X * C Polynomial.X *
        (series.map Polynomial.C) ^ 2 + X * C Polynomial.X ^ 2 *
          scaled * series.map Polynomial.C) at mapped
    simpa only [map_mul, map_add, map_sub, map_one, map_pow, evaluateX,
      evaluateVariable, evaluateLifted, imageLower] using mapped
  have upperConstant : constantCoeff upper = 1 := by simp [upper, initial]
  have lowerConstant : constantCoeff lower = 1 := by simp [lower, initial]
  have upperNonzero : upper ≠ 0 := by
    intro zero
    simp [zero] at upperConstant
  have seriesNonzero : series ≠ 0 := by
    intro zero
    simp [zero] at constant
  have sumNonzero : series + lower ≠ 0 := by
    intro zero
    have value := congrArg constantCoeff zero
    norm_num [constant, lowerConstant] at value
  have kernelZero : 1 - upper + X * upper ^ 2 * (series + lower) = 0 := by
    linear_combination -upperEquation
  rw [kernelZero, zero_mul] at evaluated
  have eliminated : series ^ 2 - upper * series + upper * lower * (series - 1) = 0 := by
    have cancelled : X * upper *
        (series ^ 2 - upper * series + upper * lower * (series - 1)) = 0 := by
      linear_combination -evaluated - kernelZero
    exact (mul_eq_zero.mp cancelled).resolve_left (mul_ne_zero X_ne_zero upperNonzero)
  have central : X * upper * series ^ 2 = series - 1 := by
    have multiplied : upper * (series + lower) *
        (X * upper * series ^ 2 - (series - 1)) = 0 := by
      linear_combination series ^ 2 * kernelZero - eliminated
    have vanishes := (mul_eq_zero.mp multiplied).resolve_left
      (mul_ne_zero upperNonzero sumNonzero)
    exact sub_eq_zero.mp vanishes
  have sameQuadratic : series = 1 + X * upper * series ^ 2 := by
    linear_combination -central
  have difference : (series - lower) * (1 - X * upper * (series + lower)) = 0 := by
    linear_combination sameQuadratic - lowerEquation
  have factorNonzero : 1 - X * upper * (series + lower) ≠ 0 := by
    intro zero
    have value := congrArg constantCoeff zero
    simp at value
  have lowerEq : lower = series := by
    exact (sub_eq_zero.mp ((mul_eq_zero.mp difference).resolve_right factorNonzero)).symm
  rw [lowerEq] at eliminated
  have relation : upper * (1 - (series - 1)) = series := by
    have multiplied : series * (upper * (1 - (series - 1)) - series) = 0 := by
      linear_combination -eliminated
    exact sub_eq_zero.mp ((mul_eq_zero.mp multiplied).resolve_left seriesNonzero)
  have functionalEquation : (series - 1) - (series - 1) ^ 2 = X * series ^ 3 := by
    linear_combination -(1 - (series - 1)) * central + X * series ^ 2 * relation
  intro degree positive
  have positiveCoefficient (index : ℕ) (nonzero : 0 < index) :
      coeff index (series - 1) = coeff index series := by
    simp only [map_sub, coeff_one, if_neg (Nat.ne_of_gt nonzero), sub_zero]
  have zeroCoefficient : coeff 0 (series - 1) = 0 := by
    simp [coeff_zero_eq_constantCoeff, constant]
  have squareCoefficient : coeff degree ((series - 1) ^ 2) =
      ∑ index ∈ Finset.Icc 1 (degree - 1),
        coeff index series * coeff (degree - index) series := by
    rw [pow_two, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun left right => coeff left (series - 1) * coeff right (series - 1)) degree]
    have inclusion : Finset.Icc 1 (degree - 1) ⊆ Finset.range (degree + 1) := by
      intro index member
      have bounds := Finset.mem_Icc.mp member
      simp only [Finset.mem_range]
      omega
    calc
      (∑ index ∈ Finset.range (degree + 1),
          coeff index (series - 1) * coeff (degree - index) (series - 1)) =
          ∑ index ∈ Finset.Icc 1 (degree - 1),
            coeff index (series - 1) * coeff (degree - index) (series - 1) := by
        apply (Finset.sum_subset inclusion ?_).symm
        intro index member excluded
        have bound := Finset.mem_range.mp member
        have endpoints : index = 0 ∨ index = degree := by
          simp only [Finset.mem_Icc, not_and_or, not_le] at excluded
          omega
        rcases endpoints with rfl | rfl <;> simp [zeroCoefficient]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro index member
        have bounds := Finset.mem_Icc.mp member
        rw [positiveCoefficient index (by omega),
          positiveCoefficient (degree - index) (by omega)]
  have cubeCoefficient : coeff (degree - 1) (series ^ 3) =
      ∑ outer ∈ Finset.HasAntidiagonal.antidiagonal (degree - 1),
        ∑ inner ∈ Finset.HasAntidiagonal.antidiagonal outer.1,
          coeff inner.1 series * coeff inner.2 series * coeff outer.2 series := by
    rw [show series ^ 3 = (series * series) * series by ring, coeff_mul]
    simp only [coeff_mul, Finset.sum_mul]
  have shiftCoefficient : coeff degree (X * series ^ 3) =
      coeff (degree - 1) (series ^ 3) := by
    simpa only [show degree - 1 + 1 = degree by omega] using
      coeff_succ_X_mul (degree - 1) (series ^ 3)
  have extracted := congrArg (coeff degree) functionalEquation
  rw [map_sub, positiveCoefficient degree (by omega), squareCoefficient,
    shiftCoefficient, cubeCoefficient] at extracted
  linear_combination extracted

end D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoKernel

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoKernel.catalytic_recurrence
