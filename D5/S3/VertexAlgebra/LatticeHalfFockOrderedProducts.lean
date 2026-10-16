/- GID: D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockOrderedProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native half-Fock coefficients have the full forward contraction expansion. -/

import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockProductKernel

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients MvPolynomial
open scoped BigOperators

noncomputable section

def pairTranslationVariable (D : LatticeData) (left right : Charge D) (index : Index D) :
    PairPolynomial D :=
  C (X index : Oscillator D) -
    C ((bilinear D left (unitCharge D index.1) : ℂ) • (1 : Oscillator D)) *
      X 0 ^ omega D index -
    C ((bilinear D right (unitCharge D index.1) : ℂ) • (1 : Oscillator D)) *
      X 1 ^ omega D index

def pairTranslation (D : LatticeData) (left right : Charge D) :
    Oscillator D →ₐ[ℂ] PairPolynomial D :=
  MvPolynomial.eval₂AlgHom ℂ (pairTranslationVariable D left right)

def secondTranslationLift (D : LatticeData) (left : Charge D) :
    Polynomial (Oscillator D) →+* PairPolynomial D :=
  Polynomial.eval₂RingHom (pairTranslation D left 0).toRingHom (MvPolynomial.X 1)

private theorem first_translation_variable (D : LatticeData) (left : Charge D)
    (index : Index D) :
    pairTranslation D left 0 (MvPolynomial.X index) =
      MvPolynomial.C (MvPolynomial.X index : Oscillator D) -
        MvPolynomial.C ((bilinear D left (unitCharge D index.1) : ℂ) • (1 : Oscillator D)) *
          MvPolynomial.X 0 ^ omega D index := by
  have zeroPairing : bilinear D (0 : Charge D) (unitCharge D index.1) = 0 := by
    simp [bilinear]
  simp only [pairTranslation, MvPolynomial.eval₂AlgHom_X, pairTranslationVariable,
    zeroPairing, Int.cast_zero, zero_smul, map_zero, zero_mul, sub_zero]

private theorem translated_scalar (D : LatticeData) (left : Charge D) (scalar : ℂ) :
    pairTranslation D left 0 (scalar • (1 : Oscillator D)) =
      MvPolynomial.C (scalar • (1 : Oscillator D)) := by
  rw [← MvPolynomial.C_eq_smul_one]
  exact (pairTranslation D left 0).commutes scalar

private theorem second_translation_variable (D : LatticeData) (left right : Charge D)
    (index : Index D) :
    secondTranslationLift D left (halfTranslationVariable D right index) =
      pairTranslationVariable D left right index := by
  unfold secondTranslationLift halfTranslationVariable
  rw [map_sub, map_mul, map_pow]
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]
  change pairTranslation D left 0 (MvPolynomial.X index) -
    pairTranslation D left 0
      ((bilinear D right (unitCharge D index.1) : ℂ) • (1 : Oscillator D)) *
        MvPolynomial.X 1 ^ omega D index = _
  rw [first_translation_variable, translated_scalar]
  rfl

theorem pair_translation_composition (D : LatticeData) (left right : Charge D)
    (polynomial : Oscillator D) :
    secondTranslationLift D left (halfTranslatedPolynomial D right polynomial) =
      pairTranslation D left right polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [secondTranslationLift, halfTranslatedPolynomial, pairTranslation]
  | add firstPolynomial secondPolynomial firstProof secondProof =>
    simp only [halfTranslatedPolynomial, pairTranslation, map_add] at firstProof secondProof ⊢
    rw [firstProof, secondProof]
  | mul_X polynomial index inductionProof =>
    simp only [halfTranslatedPolynomial, pairTranslation, map_mul,
      MvPolynomial.eval₂AlgHom_X] at inductionProof ⊢
    rw [inductionProof, second_translation_variable]

def pairConvolution (D : LatticeData) (left right : Charge D) (first second : ℤ) :
    PairPolynomial D →ₗ[Oscillator D] Oscillator D :=
  (Finsupp.lsum (Oscillator D) (fun exponent : Fin 2 →₀ ℕ =>
    LinearMap.mulRight (Oscillator D)
      (halfCreationCoeff D left (first + exponent 0) *
        halfCreationCoeff D right (second + exponent 1)))).comp
          (AddMonoidAlgebra.coeffLinearEquiv (Oscillator D)).toLinearMap

def commonKernel (D : LatticeData) (left right : Charge D) (first second : ℤ) :
    Module.End ℂ (Oscillator D) :=
  ((pairConvolution D left right first second).restrictScalars ℂ).comp
    (pairTranslation D left right).toLinearMap

private theorem convolution_expansion (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (polynomial : PairPolynomial D) :
    pairConvolution D left right first second polynomial =
      ∑ exponent ∈ polynomial.support, polynomial.coeff exponent *
        (halfCreationCoeff D left (first + exponent 0) *
          halfCreationCoeff D right (second + exponent 1)) := by
  simp only [pairConvolution, LinearMap.comp_apply, Finsupp.lsum_apply,
    Finsupp.sum, LinearMap.mulRight_apply]
  rfl

private theorem convolution_monomial (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (exponent : Fin 2 →₀ ℕ) (coefficient : Oscillator D) :
    pairConvolution D left right first second (monomial exponent coefficient) =
      coefficient * (halfCreationCoeff D left (first + exponent 0) *
        halfCreationCoeff D right (second + exponent 1)) := by
  simp [pairConvolution, MvPolynomial.monomial, mul_assoc]

private theorem convolution_C_mul (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (coefficient : Oscillator D) (polynomial : PairPolynomial D) :
    pairConvolution D left right first second (C coefficient * polynomial) =
      coefficient * pairConvolution D left right first second polynomial := by
  rw [MvPolynomial.C_mul']
  exact map_smul _ _ _

private theorem convolution_X_zero (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (degree : ℕ) (polynomial : PairPolynomial D) :
    pairConvolution D left right first second (X 0 ^ degree * polynomial) =
      pairConvolution D left right (first + degree) second polynomial := by
  classical
  induction polynomial using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]
  | monomial exponent coefficient =>
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
      convolution_monomial, convolution_monomial]
    simp only [one_mul, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), zero_add]
    congr 3
    push_cast
    omega

private theorem convolution_X_one (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (degree : ℕ) (polynomial : PairPolynomial D) :
    pairConvolution D left right first second (X 1 ^ degree * polynomial) =
      pairConvolution D left right first (second + degree) polynomial := by
  classical
  induction polynomial using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]
  | monomial exponent coefficient =>
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
      convolution_monomial, convolution_monomial]
    simp only [one_mul, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), zero_add]
    congr 3
    push_cast
    omega

private theorem kernel_expansion (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (polynomial : Oscillator D) :
    commonKernel D left right first second polynomial =
      ∑ exponent ∈ (pairTranslation D left right polynomial).support,
        (pairTranslation D left right polynomial).coeff exponent *
          (halfCreationCoeff D left (first + exponent 0) *
            halfCreationCoeff D right (second + exponent 1)) := by
  exact convolution_expansion D left right first second _

theorem kernel_constant (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (scalar : ℂ) :
    commonKernel D left right first second (C scalar) =
      C scalar * (halfCreationCoeff D left first * halfCreationCoeff D right second) := by
  have constant : pairTranslation D left right (C scalar) =
      MvPolynomial.C (MvPolynomial.C scalar) :=
    (pairTranslation D left right).commutes scalar
  change pairConvolution D left right first second (pairTranslation D left right (C scalar)) = _
  rw [constant]
  change pairConvolution D left right first second (monomial 0 (C scalar)) = _
  simpa only [Finsupp.zero_apply, Nat.cast_zero, add_zero] using
    convolution_monomial D left right first second 0 (C scalar)

theorem kernel_creator (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (polynomial : Oscillator D) (index : Index D) :
    commonKernel D left right first second (X index * polynomial) =
      X index * commonKernel D left right first second polynomial -
        (bilinear D left (unitCharge D index.1) : ℂ) •
          commonKernel D left right (first + omega D index) second polynomial -
        (bilinear D right (unitCharge D index.1) : ℂ) •
          commonKernel D left right first (second + omega D index) polynomial := by
  change pairConvolution D left right first second
    (pairTranslation D left right (X index * polynomial)) = _
  rw [← pair_translation_composition D left right (X index * polynomial)]
  rw [show halfTranslatedPolynomial D right (X index * polynomial) =
    halfTranslatedPolynomial D right (X index) * halfTranslatedPolynomial D right polynomial by
      simp only [halfTranslatedPolynomial, map_mul]]
  rw [map_mul, pair_translation_composition D left right (X index),
    pair_translation_composition D left right polynomial]
  simp only [pairTranslation, MvPolynomial.eval₂AlgHom_X, pairTranslationVariable,
    sub_mul, map_sub]
  rw [convolution_C_mul]
  simp only [mul_assoc]
  rw [convolution_C_mul, convolution_X_zero, convolution_C_mul, convolution_X_one]
  simp only [smul_mul_assoc, one_mul]
  rfl

theorem common_kernel_rectangular_support (D : LatticeData) (left right : Charge D)
    (polynomial : Oscillator D) :
    ∃ firstBound secondBound : ℤ, ∀ first second : ℤ,
      first < firstBound ∨ second < secondBound →
        commonKernel D left right first second polynomial = 0 := by
  classical
  refine ⟨-(((pairTranslation D left right polynomial).support.sup
      (fun exponent => exponent 0) : ℕ) : ℤ),
    -(((pairTranslation D left right polynomial).support.sup
      (fun exponent => exponent 1) : ℕ) : ℤ), ?_⟩
  intro first second outside
  rw [kernel_expansion]
  apply Finset.sum_eq_zero
  intro exponent supported
  rcases outside with firstOutside | secondOutside
  · have bound := Finset.le_sup (f := fun exponent : Fin 2 →₀ ℕ => exponent 0) supported
    have integerBound : (exponent 0 : ℤ) ≤
        ((pairTranslation D left right polynomial).support.sup
          (fun exponent => exponent 0) : ℕ) := by exact_mod_cast bound
    have negative : first + exponent 0 < 0 := by omega
    simp only [halfCreationCoeff, if_pos negative, zero_mul, mul_zero]
  · have bound := Finset.le_sup (f := fun exponent : Fin 2 →₀ ℕ => exponent 1) supported
    have integerBound : (exponent 1 : ℤ) ≤
        ((pairTranslation D left right polynomial).support.sup
          (fun exponent => exponent 1) : ℕ) := by exact_mod_cast bound
    have negative : second + exponent 1 < 0 := by omega
    simp only [halfCreationCoeff, if_pos negative, zero_mul, mul_zero]

theorem common_kernel_ordered_finite_support (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (polynomial : Oscillator D) :
    Function.HasFiniteSupport (fun degree : ℕ =>
      commonKernel D left right (first + degree) (second - degree) polynomial) ∧
    Function.HasFiniteSupport (fun degree : ℕ =>
      commonKernel D left right (first - degree) (second + degree) polynomial) := by
  obtain ⟨firstBound, secondBound, bound⟩ :=
    common_kernel_rectangular_support D left right polynomial
  constructor
  · apply BddAbove.finite
    refine bddAbove_def.mpr ⟨(second - secondBound).toNat, ?_⟩
    intro degree supported
    by_contra outside
    exact supported (bound _ _ (Or.inr (by omega)))
  · apply BddAbove.finite
    refine bddAbove_def.mpr ⟨(first - firstBound).toNat, ?_⟩
    intro degree supported
    by_contra outside
    exact supported (bound _ _ (Or.inl (by omega)))

end
end D5.S3.VertexAlgebra.LatticeHalfFockProductKernel

namespace D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockProductKernel
open MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

private theorem oscillator_constant (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (scalar : ℂ) :
    oscillatorCoefficient D charge (exponent - chargeNorm D charge) (C scalar) =
      C scalar * halfCreationCoeff D charge exponent := by
  rw [oscillatorCoefficient_as_sum]
  have constant : halfTranslatedPolynomial D charge (C scalar) = Polynomial.C (C scalar) := by
    simp [halfTranslatedPolynomial]
  rw [constant]
  simp [nativeCoefficientMap, Polynomial.lsum]

private def orderedTerm (D : LatticeData) (left right : Charge D) (first second : ℤ)
    (polynomial : Oscillator D) (degree : ℕ) : Oscillator D :=
  (PowerSeries.coeff degree (halfContraction D left right)) •
    commonKernel D left right (first + degree) (second - degree) polynomial

private theorem ordered_finite (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (polynomial : Oscillator D) :
    Function.HasFiniteSupport (orderedTerm D left right first second polynomial) := by
  apply (common_kernel_ordered_finite_support D left right first second polynomial).1.subset
  intro degree supported zero
  exact supported (by simp [orderedTerm, zero])

private theorem ordered_add (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (firstPolynomial secondPolynomial : Oscillator D) :
    (∑ᶠ degree : ℕ, orderedTerm D left right first second
      (firstPolynomial + secondPolynomial) degree) =
      (∑ᶠ degree : ℕ, orderedTerm D left right first second firstPolynomial degree) +
        ∑ᶠ degree : ℕ, orderedTerm D left right first second secondPolynomial degree := by
    have terms : orderedTerm D left right first second (firstPolynomial + secondPolynomial) =
        fun degree => orderedTerm D left right first second firstPolynomial degree +
          orderedTerm D left right first second secondPolynomial degree := by
      funext degree
      simp only [orderedTerm, map_add, smul_add]
    rw [terms]
    exact finsum_add_distrib (ordered_finite D left right first second firstPolynomial)
      (ordered_finite D left right first second secondPolynomial)
private theorem ordered_smul (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (scalar : ℂ) (polynomial : Oscillator D) :
    (∑ᶠ degree : ℕ, orderedTerm D left right first second (scalar • polynomial) degree) =
      scalar • ∑ᶠ degree : ℕ, orderedTerm D left right first second polynomial degree := by
    have terms : orderedTerm D left right first second (scalar • polynomial) =
        fun degree => scalar • orderedTerm D left right first second polynomial degree := by
      funext degree
      change (PowerSeries.coeff degree (halfContraction D left right)) •
        commonKernel D left right (first + degree) (second - degree) (scalar • polynomial) =
          scalar • ((PowerSeries.coeff degree (halfContraction D left right)) •
            commonKernel D left right (first + degree) (second - degree) polynomial)
      rw [map_smul]
      exact smul_comm _ _ _
    rw [terms]
    exact (smul_finsum' scalar (ordered_finite D left right first second polynomial)).symm

private def orderedExpansion (D : LatticeData) (left right : Charge D)
    (first second : ℤ) : Module.End ℂ (Oscillator D) where
  toFun polynomial := ∑ᶠ degree : ℕ, orderedTerm D left right first second polynomial degree
  map_add' := ordered_add D left right first second
  map_smul' := ordered_smul D left right first second

private theorem expansion_constant (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (scalar : ℂ) :
    oscillatorCoefficient D left (first - chargeNorm D left)
      (oscillatorCoefficient D right (second - chargeNorm D right) (C scalar)) =
        orderedExpansion D left right first second (C scalar) := by
  rw [oscillator_constant, MvPolynomial.C_mul', map_smul]
  change scalar • (∑ᶠ degree : ℕ,
    oscillatorTerm D left (first - chargeNorm D left) (halfCreationCoeff D right second) degree) = _
  rw [smul_finsum' scalar
    (charged_term_finite_support D left (first - chargeNorm D left)
      (halfCreationCoeff D right second))]
  change (∑ᶠ degree : ℕ, scalar • oscillatorTerm D left (first - chargeNorm D left)
    (halfCreationCoeff D right second) degree) = ∑ᶠ degree : ℕ, _
  apply finsum_congr
  intro degree
  rw [oscillatorTerm, half_creation_coefficient_transport]
  simp only [orderedTerm, kernel_constant, smul_mul_assoc]
  have shift : first - chargeNorm D left + chargeNorm D left + degree = first + degree := by omega
  rw [shift]
  simp only [MvPolynomial.C_mul', smul_mul_assoc]
  rw [mul_comm (halfCreationCoeff D right (second - degree))]
  exact smul_comm _ _ _

private theorem scalar_creator_algebra (D : LatticeData) (scalar firstScalar secondScalar : ℂ)
    (creator firstValue secondValue thirdValue : Oscillator D) :
    scalar • (creator * firstValue - firstScalar • secondValue - secondScalar • thirdValue) =
      creator * (scalar • firstValue) - firstScalar • (scalar • secondValue) -
        secondScalar • (scalar • thirdValue) := by
  simp only [smul_sub]
  rw [← mul_smul_comm scalar creator firstValue,
    smul_comm scalar firstScalar secondValue, smul_comm scalar secondScalar thirdValue]

private theorem scalar_kernel_creator (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (polynomial : Oscillator D) (index : Index D) (scalar : ℂ) :
    scalar • commonKernel D left right first second (X index * polynomial) =
      X index * (scalar • commonKernel D left right first second polynomial) -
        (bilinear D left (unitCharge D index.1) : ℂ) •
          (scalar • commonKernel D left right (first + omega D index) second polynomial) -
        (bilinear D right (unitCharge D index.1) : ℂ) •
          (scalar • commonKernel D left right first (second + omega D index) polynomial) := by
  calc
    _ = scalar • (X index * commonKernel D left right first second polynomial -
        (bilinear D left (unitCharge D index.1) : ℂ) •
          commonKernel D left right (first + omega D index) second polynomial -
        (bilinear D right (unitCharge D index.1) : ℂ) •
          commonKernel D left right first (second + omega D index) polynomial) :=
      congrArg (fun value : Oscillator D => scalar • value)
        (kernel_creator D left right first second polynomial index)
    _ = _ := scalar_creator_algebra D scalar _ _ _ _ _ _

private theorem ordered_creator_term (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (polynomial : Oscillator D) (index : Index D) (degree : ℕ) :
    orderedTerm D left right first second (X index * polynomial) degree =
      X index * orderedTerm D left right first second polynomial degree -
        (bilinear D left (unitCharge D index.1) : ℂ) •
          orderedTerm D left right (first + omega D index) second polynomial degree -
        (bilinear D right (unitCharge D index.1) : ℂ) •
          orderedTerm D left right first (second + omega D index) polynomial degree := by
  unfold orderedTerm
  rw [scalar_kernel_creator]
  have leftShift : first + (degree : ℤ) + omega D index =
      first + omega D index + degree := by omega
  have rightShift : second - (degree : ℤ) + omega D index =
      second + omega D index - degree := by omega
  rw [leftShift, rightShift]

private theorem creator_sum_algebra (D : LatticeData) (creator : Oscillator D)
    (firstScalar secondScalar : ℂ) (firstTerm secondTerm thirdTerm : ℕ → Oscillator D)
    (firstFinite : Function.HasFiniteSupport firstTerm)
    (secondFinite : Function.HasFiniteSupport secondTerm)
    (thirdFinite : Function.HasFiniteSupport thirdTerm) :
    (∑ᶠ degree : ℕ, (creator * firstTerm degree - firstScalar • secondTerm degree -
      secondScalar • thirdTerm degree)) =
      creator * (∑ᶠ degree : ℕ, firstTerm degree) -
        firstScalar • (∑ᶠ degree : ℕ, secondTerm degree) -
        secondScalar • (∑ᶠ degree : ℕ, thirdTerm degree) := by
  classical
  let finite := (firstFinite.union secondFinite).union thirdFinite
  let domain : Finset ℕ := finite.toFinset
  have firstContained : Function.support firstTerm ⊆ (domain : Set ℕ) := by
    intro degree supported
    exact finite.mem_toFinset.mpr (Or.inl (Or.inl supported))
  have secondContained : Function.support secondTerm ⊆ (domain : Set ℕ) := by
    intro degree supported
    exact finite.mem_toFinset.mpr (Or.inl (Or.inr supported))
  have thirdContained : Function.support thirdTerm ⊆ (domain : Set ℕ) := by
    intro degree supported
    exact finite.mem_toFinset.mpr (Or.inr supported)
  have allContained : Function.support (fun degree => creator * firstTerm degree -
      firstScalar • secondTerm degree - secondScalar • thirdTerm degree) ⊆
        (domain : Set ℕ) := by
    intro degree supported
    by_contra outside
    have firstZero : firstTerm degree = 0 := by
      by_contra nonzero
      exact outside (firstContained nonzero)
    have secondZero : secondTerm degree = 0 := by
      by_contra nonzero
      exact outside (secondContained nonzero)
    have thirdZero : thirdTerm degree = 0 := by
      by_contra nonzero
      exact outside (thirdContained nonzero)
    exact supported (by simp [firstZero, secondZero, thirdZero])
  rw [finsum_eq_sum_of_support_subset _ allContained,
    finsum_eq_sum_of_support_subset _ firstContained,
    finsum_eq_sum_of_support_subset _ secondContained,
    finsum_eq_sum_of_support_subset _ thirdContained]
  simp only [Finset.sum_sub_distrib, Finset.mul_sum, Finset.smul_sum]

private theorem expansion_creator (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (polynomial : Oscillator D) (index : Index D) :
    orderedExpansion D left right first second (X index * polynomial) =
      X index * orderedExpansion D left right first second polynomial -
        (bilinear D left (unitCharge D index.1) : ℂ) •
          orderedExpansion D left right (first + omega D index) second polynomial -
        (bilinear D right (unitCharge D index.1) : ℂ) •
          orderedExpansion D left right first (second + omega D index) polynomial := by
  change (∑ᶠ degree : ℕ, orderedTerm D left right first second (X index * polynomial) degree) = _
  calc
    _ = ∑ᶠ degree : ℕ, (
        X index * orderedTerm D left right first second polynomial degree -
          (bilinear D left (unitCharge D index.1) : ℂ) •
            orderedTerm D left right (first + omega D index) second polynomial degree -
          (bilinear D right (unitCharge D index.1) : ℂ) •
            orderedTerm D left right first (second + omega D index) polynomial degree) :=
      finsum_congr (ordered_creator_term D left right first second polynomial index)
    _ = _ := creator_sum_algebra D (X index) _ _ _ _ _
      (ordered_finite D left right first second polynomial)
      (ordered_finite D left right (first + omega D index) second polynomial)
      (ordered_finite D left right first (second + omega D index) polynomial)

theorem native_ordered_product (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (polynomial : Oscillator D) :
    oscillatorCoefficient D left (first - chargeNorm D left)
      (oscillatorCoefficient D right (second - chargeNorm D right) polynomial) =
        ∑ᶠ degree : ℕ, (PowerSeries.coeff degree (halfContraction D left right)) •
          commonKernel D left right (first + degree) (second - degree) polynomial := by
  change _ = orderedExpansion D left right first second polynomial
  induction polynomial using MvPolynomial.induction_on generalizing first second with
  | C scalar => exact expansion_constant D left right first second scalar
  | add firstPolynomial secondPolynomial firstProof secondProof =>
    simp only [map_add, firstProof, secondProof]
  | mul_X polynomial index inductionProof =>
    simp only [mul_comm polynomial (X index)]
    rw [oscillatorCoefficient_X_mul, map_sub, map_smul, oscillatorCoefficient_X_mul]
    rw [show second - chargeNorm D right + omega D index =
      second + omega D index - chargeNorm D right by omega,
      show first - chargeNorm D left + omega D index =
      first + omega D index - chargeNorm D left by omega]
    rw [inductionProof, inductionProof, inductionProof]
    exact (expansion_creator D left right first second polynomial index).symm

end
end D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
