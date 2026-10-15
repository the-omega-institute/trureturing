/- GID: D5/S3/VertexAlgebra/LatticeHalfFockGroundGenerating
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockGroundGenerating
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original corrected creation coefficients on every native ground input. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCorrectionCreationExponential
import D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
import Mathlib.Algebra.Polynomial.AlgebraMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockGroundGenerating

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFiniteCorrection
open LatticeHalfFockFockNormalField LatticeHalfFockAllStateField
open LatticeHalfFockCurrentCorrection LatticeHalfFockCorrectionCreationExponential
open MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

/- Multiplication by w^(2m) removes the negative shift of the current jet
   attached to a source axis (i,m-1). Its remaining frequencies are 2j+1.
   The coefficient is the original jetScalar, including its factorial. -/
def groundJet (D : LatticeData) (index : Index D) : PowerSeries (Oscillator D) :=
  PowerSeries.mk fun degree =>
    if degree % 2 = 1 then
      jetScalar index.2 (-((degree / 2 : ℕ) : ℤ) - 1) •
        (X (index.1, degree / 2) : Oscillator D)
    else 0

def groundEvaluation (D : LatticeData) :
    Oscillator D →ₐ[ℂ] PowerSeries (Oscillator D) :=
  MvPolynomial.eval₂AlgHom ℂ (groundJet D)

/- The correction variable becomes 1 because its shift w^(-2q) cancels
   the missing source weight q after multiplication by w^(qc+2n).
   This evaluation does not discard a term of the original Corr polynomial. -/
def correctionGroundEvaluation (D : LatticeData) :
    CorrectionPolynomial D →ₐ[ℂ] PowerSeries (Oscillator D) :=
  (Polynomial.eval₂AlgHom (groundEvaluation D) 1 (fun _ => Commute.all _ _)).comp
    (optionEquivLeft ℂ (Index D)).toAlgHom

/- The outer variable is the original source degree t; the inner variable
   is the doubled-coordinate creation degree w. -/
def originalGroundGaussian (D : LatticeData) (charge sourceCharge : Charge D) :
    PowerSeries (PowerSeries (Oscillator D)) :=
  (((PowerSeries.exp (CorrectionPolynomial D)).subst
      (originalGaussianDriver D charge sourceCharge)).map
        (correctionGroundEvaluation D).toRingHom) *
    PowerSeries.C (halfCreationExponential D charge)

private def integerCoeff (D : LatticeData) (output : ℤ) :
    PowerSeries (Oscillator D) →ₗ[ℂ] Oscillator D where
  toFun series := if output < 0 then 0 else PowerSeries.coeff output.toNat series
  map_add' first second := by
    by_cases negative : output < 0 <;> simp [negative]
  map_smul' scalar series := by
    by_cases negative : output < 0 <;> simp [negative, PowerSeries.coeff_smul]

private def groundTensor (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (ground : ActualGround D hu) :
    Oscillator D →ₗ[ℂ] ActualTensor D hu where
  toFun polynomial := chargeScalar D charge •
    (polynomial ⊗ₜ[ℂ] groundAction D hu charge ground)
  map_add' first second := by simp [TensorProduct.add_tmul, smul_add]
  map_smul' scalar polynomial := by
    simp [TensorProduct.smul_tmul', smul_comm]

private def groundReadout (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (ground : ActualGround D hu) (output : ℤ) :
    PowerSeries (Oscillator D) →ₗ[ℂ] ActualTensor D hu :=
  (groundTensor D hu charge ground).comp (integerCoeff D output)

private def wordSeries (D : LatticeData) (charge : Charge D) :
    List (Index D) → PowerSeries (Oscillator D)
  | [] => halfCreationExponential D charge
  | index :: tail => groundJet D index * wordSeries D charge tail

private def negativeCoefficient (D : LatticeData) (index : Index D)
    (series : PowerSeries (Oscillator D)) (output : ℤ) (offset : ℕ) : Oscillator D :=
  jetScalar index.2 (-(offset : ℤ) - 1) •
    ((X (index.1, offset) : Oscillator D) *
      integerCoeff D (output - (2 * (offset : ℤ) + 1)) series)

private theorem negative_coefficient_zero (D : LatticeData) (index : Index D)
    (series : PowerSeries (Oscillator D)) (output : ℤ) (offset : ℕ)
    (above : output < 2 * (offset : ℤ) + 1) :
    negativeCoefficient D index series output offset = 0 := by
  simp [negativeCoefficient, integerCoeff, show output - (2 * (offset : ℤ) + 1) < 0 by omega]

/- The range is derived from the output coefficient. Its redundant entries
   with 2j+1 > output vanish; there is no oscillator cutoff premise. -/
private theorem ground_jet_convolution (D : LatticeData) (index : Index D)
    (series : PowerSeries (Oscillator D)) (output : ℤ) :
    integerCoeff D output (groundJet D index * series) =
      ∑ offset ∈ Finset.range (output.toNat + 1),
        negativeCoefficient D index series output offset := by
  classical
  by_cases negative : output < 0
  · simp only [integerCoeff, LinearMap.coe_mk, AddHom.coe_mk, if_pos negative]
    symm
    apply Finset.sum_eq_zero
    intro offset member
    exact negative_coefficient_zero D index series output offset (by omega)
  · have nonnegative : 0 ≤ output := by omega
    have castOutput : (output.toNat : ℤ) = output := Int.toNat_of_nonneg nonnegative
    change (if output < 0 then 0 else
      PowerSeries.coeff output.toNat (groundJet D index * series)) = _
    rw [if_neg negative]
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [groundJet, PowerSeries.coeff_mk, ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    let offsets := (Finset.range (output.toNat + 1)).filter
      (fun offset => 2 * offset + 1 ≤ output.toNat)
    have reindex :
        (∑ degree ∈ (Finset.range (output.toNat + 1)).filter (fun degree => degree % 2 = 1),
          (jetScalar index.2 (-((degree / 2 : ℕ) : ℤ) - 1) •
            (X (index.1, degree / 2) : Oscillator D)) * PowerSeries.coeff (output.toNat - degree) series) =
        ∑ offset ∈ offsets, negativeCoefficient D index series output offset := by
      apply Finset.sum_bij (fun degree _ => degree / 2)
      · intro degree member
        simp only [Finset.mem_filter, Finset.mem_range] at member
        simp only [offsets, Finset.mem_filter, Finset.mem_range]
        omega
      · intro first firstMember second secondMember equality
        simp only [Finset.mem_filter, Finset.mem_range] at firstMember secondMember
        omega
      · intro offset member
        simp only [offsets, Finset.mem_filter, Finset.mem_range] at member
        refine ⟨2 * offset + 1, ?_, by omega⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      · intro degree member
        simp only [Finset.mem_filter, Finset.mem_range] at member
        have oddDegree : 2 * (degree / 2) + 1 = degree := by omega
        have lower : 0 ≤ output - (2 * ((degree / 2 : ℕ) : ℤ) + 1) := by omega
        have remaining :
            (output - (2 * ((degree / 2 : ℕ) : ℤ) + 1)).toNat = output.toNat - degree := by omega
        simp only [negativeCoefficient, integerCoeff, LinearMap.coe_mk, AddHom.coe_mk,
          if_neg (not_lt.mpr lower), remaining, smul_mul_assoc]
    rw [reindex]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro offset member outside
    have above : output < 2 * (offset : ℤ) + 1 := by
      simp only [offsets, Finset.mem_filter, member, true_and, not_le] at outside
      omega
    exact negative_coefficient_zero D index series output offset above

private theorem current_ground (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) (mode : ℕ) (ground : ActualGround D hu) :
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour (mode : ℤ)
      ((1 : Oscillator D) ⊗ₜ[ℂ] ground) = 0 := by
  have annihilates : LatticeActualAnnihilation.annihilate D colour mode (1 : Oscillator D) = 0 := by
    rw [← LatticeActualAnnihilation.annihilation_apply]
    exact Derivation.map_one_eq_zero _
  simp [LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd, LatticeHalfFock.current,
    show ¬ (mode : ℤ) < 0 by omega, annihilates]

private theorem normal_word_ground (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (word : List (Index D)) (output : ℤ) (ground : ActualGround D hu) :
    (normalWord D hu charge word).coeff
        (output - chargeNorm D charge - 2 * (wordWeight D word : ℤ))
        ((1 : Oscillator D) ⊗ₜ[ℂ] ground) =
      groundReadout D hu charge ground output (wordSeries D charge word) := by
  classical
  induction word generalizing output with
  | nil =>
    simpa [normalWord, wordSeries, wordWeight, groundReadout, groundTensor,
      integerCoeff, halfCreationCoeff] using
      charged_vacuum_coefficient D hu charge (output - chargeNorm D charge) ground
  | cons index tail inductionProof =>
    let exponent := output - chargeNorm D charge - 2 * (wordWeight D (index :: tail) : ℤ)
    have positiveZero (offset : ℕ) :
        positiveTerm D hu index (normalWord D hu charge tail) exponent
          ((1 : Oscillator D) ⊗ₜ[ℂ] ground) offset = 0 := by
      simp [positiveTerm, current_ground D hu index.1 offset ground]
    have negativeValue (offset : ℕ) :
        negativeTerm D hu index (normalWord D hu charge tail) exponent
          ((1 : Oscillator D) ⊗ₜ[ℂ] ground) offset =
        groundTensor D hu charge ground
          (negativeCoefficient D index (wordSeries D charge tail) output offset) := by
      have shifted : exponent - 2 * (offset : ℤ) + 2 * (index.2 : ℤ) + 1 =
          (output - (2 * (offset : ℤ) + 1)) - chargeNorm D charge -
            2 * (wordWeight D tail : ℤ) := by
        simp only [exponent, wordWeight, List.map_cons, List.sum_cons, sourceWeight,
          Nat.cast_add, Nat.cast_one]
        ring
      rw [negativeTerm, shifted, inductionProof]
      simp only [groundReadout, LinearMap.comp_apply, groundTensor, LinearMap.coe_mk,
        AddHom.coe_mk, map_smul, LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd,
        TensorProduct.map_tmul, LinearMap.id_apply, LatticeHalfFock.current_negative,
        LinearMap.mulLeft_apply, negativeCoefficient]
      rw [TensorProduct.smul_tmul']
      exact smul_comm _ _ _
    change (normalInsertion D hu index (normalWord D hu charge tail)).coeff exponent
      ((1 : Oscillator D) ⊗ₜ[ℂ] ground) = _
    simp only [normalInsertion, HVertexOperator.coeff_of_coeff, normalCoefficient,
      LinearMap.coe_mk, AddHom.coe_mk]
    change (∑ᶠ offset : ℕ, negativeTerm D hu index (normalWord D hu charge tail) exponent
        ((1 : Oscillator D) ⊗ₜ[ℂ] ground) offset) +
        (∑ᶠ offset : ℕ, positiveTerm D hu index (normalWord D hu charge tail) exponent
          ((1 : Oscillator D) ⊗ₜ[ℂ] ground) offset) = _
    simp_rw [positiveZero]
    rw [finsum_zero, add_zero]
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (output.toNat + 1)) (by
      intro offset nonzero
      by_contra outside
      have above : output < 2 * (offset : ℤ) + 1 := by
        simp only [Finset.mem_coe, Finset.mem_range, not_lt] at outside
        omega
      exact nonzero (by rw [negativeValue, negative_coefficient_zero D index _ output offset above,
        map_zero]))]
    simp_rw [negativeValue]
    rw [← map_sum, ← ground_jet_convolution]
    rfl

private theorem occurrence_product (D : LatticeData) (exponent : Index D →₀ ℕ) :
    ((LatticeAllStateField.occurrences D exponent).map (groundJet D)).prod =
      exponent.prod (fun index count => groundJet D index ^ count) := by
  classical
  rw [LatticeAllStateField.occurrences, Multiset.prod_map_toList,
    Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (by intro; simp) (by intros; rw [pow_add])]

private theorem word_series_monomial (D : LatticeData) (charge : Charge D)
    (exponent : Index D →₀ ℕ) :
    wordSeries D charge (LatticeAllStateField.occurrences D exponent) =
      groundEvaluation D (monomial exponent 1) * halfCreationExponential D charge := by
  have product (word : List (Index D)) :
      wordSeries D charge word = (word.map (groundJet D)).prod * halfCreationExponential D charge := by
    induction word with
    | nil => simp [wordSeries]
    | cons index tail inductionProof => simp [wordSeries, inductionProof, mul_assoc]
  rw [product, occurrence_product]
  simp [groundEvaluation, MvPolynomial.eval₂_monomial]

private theorem normal_polynomial_ground (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Oscillator D) (degree : ℕ)
    (homogeneous : ∀ exponent ∈ polynomial.support,
      Finsupp.weight (sourceWeight D) exponent = degree)
    (output : ℤ) (ground : ActualGround D hu) :
    (normalPolynomial D hu charge polynomial).coeff
        (output - chargeNorm D charge - 2 * (degree : ℤ))
        ((1 : Oscillator D) ⊗ₜ[ℂ] ground) =
      groundReadout D hu charge ground output
        (groundEvaluation D polynomial * halfCreationExponential D charge) := by
  classical
  have expansion := normalPolynomial_enumerated_expansion D hu charge polynomial
    (LatticeAllStateField.occurrences D) (by intro exponent member; exact List.Perm.refl _)
  rw [expansion]
  simp only [map_sum, Finset.sum_apply, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, Pi.smul_apply]
  have evaluated : groundEvaluation D polynomial * halfCreationExponential D charge =
      ∑ exponent ∈ polynomial.support, coeff exponent polynomial •
        (groundEvaluation D (monomial exponent 1) * halfCreationExponential D charge) := by
    conv_lhs => rw [MvPolynomial.as_sum polynomial]
    simp only [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro exponent member
    rw [show monomial exponent (coeff exponent polynomial) =
      coeff exponent polynomial • monomial exponent (1 : ℂ) by simp [smul_monomial],
      map_smul, smul_mul_assoc]
  rw [evaluated, map_sum]
  apply Finset.sum_congr rfl
  intro exponent member
  rw [map_smul, ← word_series_monomial]
  congr 1
  rw [← homogeneous exponent member, ← wordWeight_occurrences]
  exact normal_word_ground D hu charge _ output ground

private def corrGroundSum (D : LatticeData) :
    (ℕ →₀ Oscillator D) →ₗ[ℂ] PowerSeries (Oscillator D) :=
  Finsupp.lsum ℂ (fun _ : ℕ => (groundEvaluation D).toLinearMap)

private theorem correction_ground_sum (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) :
    correctionGroundEvaluation D (correctionLift D charge polynomial) =
      corrGroundSum D (Corr D charge polynomial) := by
  change Polynomial.eval₂ (groundEvaluation D).toRingHom 1
      (optionEquivLeft ℂ (Index D) (correctionLift D charge polynomial)) = _
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  simp only [one_pow, mul_one]
  rfl

/- Both indices are unrestricted. The finite shift range is supplied by
   the original correction grading, and each coefficient of a jet product
   is a finite natural antidiagonal. Negative output degrees vanish on
   every ground vector. This formula retains the Gaussian without replacing
   its scalar part by a binomial-unit expression. -/
theorem original_creation_ground_gaussian (D : LatticeData) (hu : IsUnit D.G.det)
    (charge sourceCharge : Charge D) (degree : ℕ) (output : ℤ) (ground : ActualGround D hu) :
    (Ytw D hu (Finsupp.single charge (creationCoeff D sourceCharge (degree : ℤ)))).coeff
        (output - chargeNorm D charge - 2 * (degree : ℤ))
        ((1 : Oscillator D) ⊗ₜ[ℂ] ground) =
      chargeScalar D charge •
        ((if output < 0 then 0 else PowerSeries.coeff output.toNat
          (PowerSeries.coeff degree (originalGroundGaussian D charge sourceCharge))) ⊗ₜ[ℂ]
            groundAction D hu charge ground) ∧
    PowerSeries.coeff degree (originalGroundGaussian D charge sourceCharge) =
      (∑ shift ∈ Finset.range (degree + 1),
        groundEvaluation D
          ((optionEquivLeft ℂ (Index D)
            (PowerSeries.coeff degree
              ((PowerSeries.exp (CorrectionPolynomial D)).subst
                (originalGaussianDriver D charge sourceCharge)))).coeff shift)) *
        halfCreationExponential D charge := by
  classical
  let source := creationCoeff D sourceCharge (degree : ℤ)
  let corrected := Corr D charge source
  have grading := creation_corr_finite_coefficient D charge sourceCharge degree
  have finiteCorr : corrected = ∑ shift ∈ Finset.range (degree + 1),
      Finsupp.single shift (corrected shift) := grading.2.2
  have gaussianCoefficient :
      PowerSeries.coeff degree (originalGroundGaussian D charge sourceCharge) =
        (∑ shift ∈ Finset.range (degree + 1), groundEvaluation D (corrected shift)) *
          halfCreationExponential D charge := by
    rw [originalGroundGaussian, PowerSeries.coeff_mul_C, PowerSeries.coeff_map,
      ← (original_creation_coefficient_gaussian D charge sourceCharge degree 0).1,
      correction_ground_sum]
    change corrGroundSum D corrected * halfCreationExponential D charge = _
    rw [finiteCorr]
    simp only [corrGroundSum, map_sum, Finsupp.lsum_single, AlgHom.toLinearMap_apply]
  constructor
  · change (Ytw D hu (Finsupp.single charge source)).coeff
        (output - chargeNorm D charge - 2 * (degree : ℤ))
        ((1 : Oscillator D) ⊗ₜ[ℂ] ground) =
      groundReadout D hu charge ground output
        (PowerSeries.coeff degree (originalGroundGaussian D charge sourceCharge))
    simp only [Ytw, Finsupp.lsum_single, correctedPolynomial, LinearMap.comp_apply]
    change (Finsupp.lsum ℂ (fun shift : ℕ =>
      (shiftLinear D hu shift).comp (normalPolynomial D hu charge)) corrected).coeff
        (output - chargeNorm D charge - 2 * (degree : ℤ))
        ((1 : Oscillator D) ⊗ₜ[ℂ] ground) = _
    rw [finiteCorr]
    simp only [map_sum, Finsupp.lsum_single, LinearMap.comp_apply, Finset.sum_apply,
      LinearMap.sum_apply, shiftLinear, shiftField, LinearMap.coe_mk, AddHom.coe_mk,
      HVertexOperator.coeff_of_coeff]
    rw [gaussianCoefficient, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro shift member
    have shiftBound : shift ≤ degree := by
      simp only [Finset.mem_range] at member
      omega
    have residualWeight : ∀ exponent ∈ (corrected shift).support,
        Finsupp.weight (sourceWeight D) exponent = degree - shift := by
      intro exponent member
      have nonzero := MvPolynomial.mem_support_iff.mp member
      have conserved := (grading.2.1 shift exponent nonzero).1
      omega
    rw [show output - chargeNorm D charge - 2 * (degree : ℤ) + 2 * (shift : ℤ) =
        output - chargeNorm D charge - 2 * ((degree - shift : ℕ) : ℤ) by omega]
    exact normal_polynomial_ground D hu charge (corrected shift) (degree - shift)
      residualWeight output ground
  · rw [gaussianCoefficient]
    apply congrArg (fun series : PowerSeries (Oscillator D) =>
      series * halfCreationExponential D charge)
    apply Finset.sum_congr rfl
    intro shift member
    rw [show corrected shift = Corr D charge
      (creationCoeff D sourceCharge (degree : ℤ)) shift from rfl,
      (original_creation_coefficient_gaussian D charge sourceCharge degree shift).2.1]

end
end D5.S3.VertexAlgebra.LatticeHalfFockGroundGenerating
