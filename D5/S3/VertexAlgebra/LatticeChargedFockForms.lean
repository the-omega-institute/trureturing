/- GID: D5/S3/VertexAlgebra/LatticeChargedFockForms
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeChargedFockForms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coefficient conjugation and charge-selected forms on the full native carrier. -/

import D5.S3.VertexAlgebra.LatticeOscillatorFockForm
import D5.S3.VertexAlgebra.LatticeInvolution
import D5.S3.VertexAlgebra.LatticeConvolutionFockAdjoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.LatticeChargedFockForms

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeOscillatorFockForm LatticeSugawaraCurrents
open LatticeActualProductKernel LatticeActualGeneratorLocality LatticeConvolutionFockAdjoint
open MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

def coefficientConjugation (D : LatticeData) : Carrier D →ₗ⋆[ℂ] Carrier D :=
  Finsupp.mapRange.linearMap (conjugatePolynomial D)

def pct (D : LatticeData) : Carrier D →ₗ⋆[ℂ] Carrier D :=
  (LatticeInvolution.thetaLinear D).comp (coefficientConjugation D)

def hermitianForm (D : LatticeData) : Carrier D →ₗ⋆[ℂ] Carrier D →ₗ[ℂ] ℂ where
  toFun left := Finsupp.lsum ℂ (fun charge => fockForm D (left charge))
  map_add' := by
    intro left right
    simp only [Finsupp.add_apply, map_add]
    change Finsupp.lsum ℂ ((fun charge => fockForm D (left charge)) +
      (fun charge => fockForm D (right charge))) = _
    exact map_add (Finsupp.lsum ℂ) _ _
  map_smul' := by
    intro scalar left
    simp only [Finsupp.smul_apply, LinearMap.map_smulₛₗ]
    change Finsupp.lsum ℂ ((starRingEnd ℂ scalar) •
      (fun charge => fockForm D (left charge))) = _
    exact map_smul (Finsupp.lsum ℂ) _ _

def bpzForm (D : LatticeData) : Carrier D →ₗ[ℂ] Carrier D →ₗ[ℂ] ℂ :=
  (hermitianForm D).comp (pct D)

private theorem conjugation_single (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) :
    coefficientConjugation D (Finsupp.single charge polynomial) =
      Finsupp.single charge (conjugatePolynomial D polynomial) := by
  simp [coefficientConjugation, Finsupp.mapRange.linearMap]

private theorem hermitian_single (D : LatticeData) (leftCharge rightCharge : Charge D)
    (left right : Oscillator D) :
    hermitianForm D (Finsupp.single leftCharge left) (Finsupp.single rightCharge right) =
      if leftCharge = rightCharge then fockForm D left right else 0 := by
  classical
  by_cases matching : leftCharge = rightCharge
  · subst rightCharge
    simp [hermitianForm, Finsupp.lsum_single, Finsupp.single_apply]
  · simp [hermitianForm, Finsupp.lsum_single, Finsupp.single_apply,
      matching, Ne.symm matching]

private theorem conjugate_neutral_polynomial (D : LatticeData) (axis : Fin D.rank)
    (charge : Charge D) (mode : ℤ) (polynomial : Oscillator D) :
    conjugatePolynomial D (neutralPolynomialMode D axis charge mode polynomial) =
      neutralPolynomialMode D axis charge mode (conjugatePolynomial D polynomial) := by
  classical
  by_cases negative : mode < 0
  · have index : mode = -(((-mode - 1).toNat : ℕ) : ℤ) - 1 := by omega
    rw [index]
    simp only [neutralPolynomialMode_negative, LinearMap.mulLeft_apply]
    apply LatticeOscillatorFockForm.conjugatePolynomial_X_mul
  · by_cases zero_mode : mode = 0
    · simp [neutralPolynomialMode, negative, zero_mode, conjugatePolynomial,
        LinearMap.smul_apply, MvPolynomial.smul_eq_C_mul]
    · have index : mode = (((mode - 1).toNat : ℕ) : ℤ) + 1 := by omega
      rw [index]
      simp only [neutralPolynomialMode_positive, LinearMap.smul_apply]
      change conjugatePolynomial D (annihilator D (axis, (mode - 1).toNat) polynomial) =
        annihilator D (axis, (mode - 1).toNat) (conjugatePolynomial D polynomial)
      apply LatticeOscillatorFockForm.annihilator_conjugate

private theorem conjugation_neutral (D : LatticeData) (axis : Fin D.rank)
    (mode : ℤ) (state : Carrier D) :
    coefficientConjugation D (neutralMode D axis mode state) =
      neutralMode D axis mode (coefficientConjugation D state) := by
  classical
  induction state using Finsupp.induction_linear with
  | zero => simp
  | add left right left_induction right_induction =>
      simp [map_add, left_induction, right_induction]
  | single charge polynomial =>
      simp only [neutralMode, Finsupp.lsum_single, LinearMap.comp_apply,
        Finsupp.lsingle_apply, conjugation_single]
      rw [conjugate_neutral_polynomial]

theorem pct_neutral (D : LatticeData) (axis : Fin D.rank) (mode : ℤ) (state : Carrier D) :
    pct D (neutralMode D axis mode state) = -neutralMode D axis mode (pct D state) := by
  simp only [pct, LinearMap.comp_apply, conjugation_neutral]
  exact LatticeInvolution.theta_neutralMode D axis mode (coefficientConjugation D state)

private theorem neutral_polynomial_adjoint (D : LatticeData) (axis : Fin D.rank)
    (charge : Charge D) (mode : ℤ) (left right : Oscillator D) :
    fockForm D (neutralPolynomialMode D axis charge mode left) right =
      fockForm D left (neutralPolynomialMode D axis charge (-mode) right) := by
  by_cases negative : mode < 0
  · have index : mode = -(((-mode - 1).toNat : ℕ) : ℤ) - 1 := by omega
    have opposite : -mode = (((-mode - 1).toNat : ℕ) : ℤ) + 1 := by omega
    simpa only [← index, ← opposite] using
      fockForm_creation_adjoint D charge axis (-mode - 1).toNat left right
  · by_cases zero_mode : mode = 0
    · subst mode
      simp [neutralPolynomialMode, LinearMap.smul_apply, LinearMap.map_smulₛₗ,
        LinearMap.smul_apply]
    · have index : mode = (((mode - 1).toNat : ℕ) : ℤ) + 1 := by omega
      have opposite : -mode = -(((mode - 1).toNat : ℕ) : ℤ) - 1 := by omega
      simpa only [← index, ← opposite] using
        fockForm_annihilation_adjoint D charge axis (mode - 1).toNat left right

theorem hermitian_neutral (D : LatticeData) (axis : Fin D.rank) (mode : ℤ)
    (left right : Carrier D) :
    hermitianForm D (neutralMode D axis mode left) right =
      hermitianForm D left (neutralMode D axis (-mode) right) := by
  classical
  induction left using Finsupp.induction_linear with
  | zero => simp
  | add first second first_induction second_induction =>
      simp only [map_add, LinearMap.add_apply, first_induction, second_induction]
  | single leftCharge leftPolynomial =>
      induction right using Finsupp.induction_linear with
      | zero => simp
      | add first second first_induction second_induction =>
          simp only [map_add, LinearMap.add_apply, first_induction, second_induction]
      | single rightCharge rightPolynomial =>
          simp only [neutralMode_single, hermitian_single]
          by_cases same_charge : leftCharge = rightCharge
          · subst rightCharge
            simp only [if_true]
            exact neutral_polynomial_adjoint D axis leftCharge mode leftPolynomial rightPolynomial
          · simp [same_charge]

theorem bpz_neutral (D : LatticeData) (axis : Fin D.rank) (mode : ℤ)
    (left right : Carrier D) :
    bpzForm D (neutralMode D axis mode left) right =
      -bpzForm D left (neutralMode D axis (-mode) right) := by
  simp only [bpzForm, LinearMap.comp_apply, pct_neutral, map_neg,
    LinearMap.neg_apply, hermitian_neutral]

private theorem epsilon_real (D : LatticeData) (left right : Charge D) :
    star (epsilon D left right) = epsilon D left right := by
  unfold epsilon paritySign
  split_ifs <;> simp

private theorem epsilon_neg_left (D : LatticeData) (left right : Charge D) :
    epsilon D (-left) right = epsilon D left right := by
  have negative : lowerCocycleExponent D (-left) right = -lowerCocycleExponent D left right := by
    simp only [lowerCocycleExponent, Pi.neg_apply, mul_neg, neg_mul,
      Finset.sum_neg_distrib]
    ring
  change paritySign (lowerCocycleExponent D (-left) right) =
    paritySign (lowerCocycleExponent D left right)
  rw [negative]
  simp [paritySign]

private theorem epsilon_adjoint_phase (D : LatticeData) (charge sector : Charge D) :
    epsilon D charge sector = paritySign (bilinear D charge charge / 2) *
      epsilon D (-charge) (charge + sector) := by
  have self_phase : epsilon D charge charge = paritySign (bilinear D charge charge / 2) := by
    unfold epsilon
    rw [LatticeTwistedGroundRealization.SignQuotient.integral_cocycle_square]
  simp only [epsilon_add_right, epsilon_neg_left, self_phase]
  rw [← mul_assoc, paritySign_square, one_mul]

private theorem hermitian_raw (D : LatticeData) (charge : Charge D) (index : ℤ)
    (left right : Carrier D) :
    hermitianForm D (rawCoeff D charge index left) right =
      paritySign (bilinear D charge charge / 2) *
        hermitianForm D left (rawCoeff D (-charge) (-index - bilinear D charge charge) right) := by
  classical
  induction left using Finsupp.induction_linear with
  | zero => simp
  | add first second first_induction second_induction =>
      simp [map_add, LinearMap.add_apply, first_induction, second_induction, mul_add]
  | single leftCharge leftPolynomial =>
      induction right using Finsupp.induction_linear with
      | zero => simp
      | add first second first_induction second_induction =>
          simp [map_add, first_induction, second_induction, mul_add]
      | single rightCharge rightPolynomial =>
          by_cases matching : rightCharge = charge + leftCharge
          · subst rightCharge
            have sector : -charge + (charge + leftCharge) = leftCharge := by abel
            have reflected : (-index - bilinear D charge charge) -
                bilinear D (-charge) (charge + leftCharge) =
                  -(index - bilinear D charge leftCharge) := by
              rw [bilinear_neg_left, bilinear_add_right]
              ring
            simp only [raw_single_convolution, LinearMap.map_smulₛₗ,
              LinearMap.smul_apply, starRingEnd_apply, epsilon_real, map_smul,
              hermitian_single, sector, if_true]
            rw [reflected, convolution_transpose, epsilon_adjoint_phase D charge leftCharge]
            simp only [smul_eq_mul]
            ring
          · have reverse_mismatch : leftCharge ≠ -charge + rightCharge := by
              intro equality
              apply matching
              rw [equality]
              abel
            simp [raw_single_convolution, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
              map_smul, hermitian_single, Ne.symm matching, reverse_mismatch]

theorem hermitian_charged (D : LatticeData) (charge : Charge D) (mode : ℤ)
    (left right : Carrier D) :
    hermitianForm D (((actualField D charge)[[mode]]) left) right =
      paritySign (bilinear D charge charge / 2) *
        hermitianForm D left
          (((actualField D (-charge))[[bilinear D charge charge - mode - 2]]) right) := by
  rw [actual_modes, actual_modes]
  have reflected : -(bilinear D charge charge - mode - 2) - 1 =
      -(-mode - 1) - bilinear D charge charge := by ring
  rw [reflected]
  exact hermitian_raw D charge (-mode - 1) left right

private def conjugationRing (D : LatticeData) : Oscillator D →+* Oscillator D :=
  MvPolynomial.map (starRingEnd ℂ)

private theorem conjugation_X (D : LatticeData) (coordinate : Index D) :
    conjugationRing D (X coordinate) = X coordinate := by
  simp [conjugationRing]

private theorem conjugation_creationSeries (D : LatticeData) (charge : Charge D) :
    PowerSeries.map (conjugationRing D) (creationSeries D charge) = creationSeries D charge := by
  apply PowerSeries.ext
  intro degree
  simp only [PowerSeries.coeff_map, creationSeries, PowerSeries.coeff_mk]
  split_ifs <;> simp [conjugationRing, MvPolynomial.smul_eq_C_mul]

private theorem conjugation_creationExponential (D : LatticeData) (charge : Charge D) :
    PowerSeries.map (conjugationRing D) (creationExponential D charge) =
      creationExponential D charge := by
  have substitutable : PowerSeries.HasSubst (creationSeries D charge) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply])
  have mapped := PowerSeries.map_subst (h := conjugationRing D) substitutable
    (PowerSeries.exp (Oscillator D))
  change PowerSeries.map (conjugationRing D) (creationExponential D charge) =
    (PowerSeries.map (conjugationRing D) (PowerSeries.exp (Oscillator D))).subst
      (PowerSeries.map (conjugationRing D) (creationSeries D charge)) at mapped
  rw [mapped, PowerSeries.map_exp, conjugation_creationSeries] <;> rfl

private theorem conjugation_creationCoeff (D : LatticeData) (charge : Charge D) (index : ℤ) :
    conjugationRing D (creationCoeff D charge index) = creationCoeff D charge index := by
  unfold creationCoeff
  split_ifs
  · exact map_zero _
  · rw [← PowerSeries.coeff_map, conjugation_creationExponential]

private theorem conjugation_translationVariable (D : LatticeData) (charge : Charge D)
    (coordinate : Index D) :
    Polynomial.map (conjugationRing D) (translationVariable D charge coordinate.1 coordinate.2) =
      translationVariable D charge coordinate.1 coordinate.2 := by
  simp [translationVariable, conjugationRing, MvPolynomial.smul_eq_C_mul]

private theorem conjugation_translation (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) :
    Polynomial.map (conjugationRing D) (translatedPolynomial D charge polynomial) =
      translatedPolynomial D charge (conjugationRing D polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [translatedPolynomial, conjugationRing]
  | add first second first_induction second_induction =>
      simp only [translatedPolynomial, map_add, Polynomial.map_add] at first_induction second_induction ⊢
      rw [first_induction, second_induction]
  | mul_X polynomial coordinate induction_hypothesis =>
      simp only [translatedPolynomial, map_mul, Polynomial.map_mul,
        conjugation_X, eval₂Hom_X'] at induction_hypothesis ⊢
      rw [induction_hypothesis, conjugation_translationVariable]

private theorem conjugation_convolution (D : LatticeData) (charge : Charge D) (index : ℤ)
    (polynomial : Polynomial (Oscillator D)) :
    conjugationRing D (convolution D charge index polynomial) =
      convolution D charge index (Polynomial.map (conjugationRing D) polynomial) := by
  induction polynomial using Polynomial.induction_on' with
  | add first second first_induction second_induction =>
      simp only [map_add, Polynomial.map_add, first_induction, second_induction]
  | monomial degree coefficient =>
      rw [convolution_monomial, map_mul, conjugation_creationCoeff,
        Polynomial.map_monomial, convolution_monomial]

private theorem conjugation_raw (D : LatticeData) (charge : Charge D) (index : ℤ) (state : Carrier D) :
    coefficientConjugation D (rawCoeff D charge index state) =
      rawCoeff D charge index (coefficientConjugation D state) := by
  classical
  induction state using Finsupp.induction_linear with
  | zero => simp
  | add first second first_induction second_induction =>
      simp [map_add, first_induction, second_induction]
  | single sector polynomial =>
      simp only [raw_single_convolution, LinearMap.map_smulₛₗ,
        conjugation_single, starRingEnd_apply]
      change star (epsilon D charge sector) • Finsupp.single (charge + sector)
          (conjugationRing D (convolution D charge (index - bilinear D charge sector)
            (translatedPolynomial D charge polynomial))) =
        epsilon D charge sector • Finsupp.single (charge + sector)
          (convolution D charge (index - bilinear D charge sector)
            (translatedPolynomial D charge (conjugationRing D polynomial)))
      rw [epsilon_real, conjugation_convolution, conjugation_translation]

private theorem pct_raw (D : LatticeData) (charge : Charge D) (index : ℤ) (state : Carrier D) :
    pct D (rawCoeff D charge index state) = rawCoeff D (-charge) index (pct D state) := by
  simp only [pct, LinearMap.comp_apply, conjugation_raw]
  exact LatticeInvolution.theta_rawCoeff D charge index (coefficientConjugation D state)

private theorem pct_charged (D : LatticeData) (charge : Charge D) (mode : ℤ) (state : Carrier D) :
    pct D (((actualField D charge)[[mode]]) state) =
      ((actualField D (-charge))[[mode]]) (pct D state) := by
  rw [actual_modes, actual_modes]
  exact pct_raw D charge (-mode - 1) state

theorem bpz_charged (D : LatticeData) (charge : Charge D) (mode : ℤ)
    (left right : Carrier D) :
    bpzForm D (((actualField D charge)[[mode]]) left) right =
      paritySign (bilinear D charge charge / 2) * bpzForm D left
        (((actualField D charge)[[bilinear D charge charge - mode - 2]]) right) := by
  simp only [bpzForm, LinearMap.comp_apply, pct_charged, hermitian_charged,
    LatticeInvolution.bilinear_neg_neg, neg_neg]

end
end D5.S3.VertexAlgebra.LatticeChargedFockForms
