/- GID: D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockOrderedProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual half-Fock coefficient products have both supported contraction expansions. -/


import D5.S3.VertexAlgebra.LatticeHalfFockProductKernel
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockProductKernel
open LatticeActualProductKernel MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

private theorem oscillator_convolution (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (polynomial : Oscillator D) :
    oscillatorCoefficient D charge (exponent - chargeNorm D charge) polynomial =
      coefficientConvolution (halfCreationCoeff D charge) exponent
        (halfTranslatedPolynomial D charge polynomial) := by
  classical
  change (∑ᶠ degree : ℕ,
    oscillatorTerm D charge (exponent - chargeNorm D charge) polynomial degree) = _
  rw [finsum_eq_sum_of_support_subset _
    (term_support D charge (exponent - chargeNorm D charge) polynomial),
    coefficientConvolution_expansion]
  apply Finset.sum_congr rfl
  intro degree supported
  change (halfTranslatedPolynomial D charge polynomial).coeff degree *
    halfCreationCoeff D charge (exponent - chargeNorm D charge + chargeNorm D charge + degree) =
      (halfTranslatedPolynomial D charge polynomial).coeff degree * halfCreationCoeff D charge (exponent + degree)
  rw [show exponent - chargeNorm D charge + chargeNorm D charge + degree = exponent + degree by omega]

private theorem oscillator_constant (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (scalar : ℂ) :
    oscillatorCoefficient D charge (exponent - chargeNorm D charge) (C scalar) =
      C scalar * halfCreationCoeff D charge exponent := by
  rw [oscillator_convolution]
  have constant : halfTranslatedPolynomial D charge (C scalar) = Polynomial.C (C scalar) := by
    simp [halfTranslatedPolynomial]
  rw [constant]
  change coefficientConvolution (halfCreationCoeff D charge) exponent
    (Polynomial.monomial 0 (C scalar)) = _
  simpa using coefficientConvolution_monomial (halfCreationCoeff D charge) exponent 0 (C scalar)

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
  have leftShift : first + (degree : ℤ) + omega D index = first + omega D index + degree := by omega
  have rightShift : second - (degree : ℤ) + omega D index = second + omega D index - degree := by omega
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
    rw [oscillator_coefficient_X_mul, map_sub, map_smul, oscillator_coefficient_X_mul]
    rw [show second - chargeNorm D right + omega D index =
      second + omega D index - chargeNorm D right by omega,
      show first - chargeNorm D left + omega D index =
        first + omega D index - chargeNorm D left by omega]
    rw [inductionProof, inductionProof, inductionProof]
    exact (expansion_creator D left right first second polynomial index).symm

end
end D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
