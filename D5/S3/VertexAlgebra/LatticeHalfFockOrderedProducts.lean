/- GID: D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockOrderedProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual half-Fock coefficient products have both supported contraction expansions. -/


import D5.S3.VertexAlgebra.LatticeHalfFockProductKernel
import D5.S3.VertexAlgebra.LatticeHalfFockGroundProducts
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockProductKernel
open LatticeHalfFockGroundProducts
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

private theorem oscillator_creator (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (polynomial : Oscillator D) (index : Index D) :
    oscillatorCoefficient D charge (exponent - chargeNorm D charge) (X index * polynomial) =
      X index * oscillatorCoefficient D charge (exponent - chargeNorm D charge) polynomial -
        (bilinear D charge (unitCharge D index.1) : ℂ) •
          oscillatorCoefficient D charge (exponent + omega D index - chargeNorm D charge)
            polynomial := by
  rw [oscillator_convolution, oscillator_convolution, oscillator_convolution]
  have translation : halfTranslatedPolynomial D charge (X index * polynomial) =
      halfTranslationVariable D charge index * halfTranslatedPolynomial D charge polynomial := by
    simp [halfTranslatedPolynomial]
  rw [translation]
  simp only [halfTranslationVariable, sub_mul, map_sub, mul_assoc]
  rw [coefficientConvolution_C_mul, coefficientConvolution_C_mul,
    coefficientConvolution_X_pow]
  simp only [smul_mul_assoc, one_mul]

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
    rw [oscillator_creator, map_sub, map_smul, oscillator_creator]
    rw [inductionProof, inductionProof, inductionProof]
    exact (expansion_creator D left right first second polynomial index).symm

theorem native_reverse_ordered_product (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (polynomial : Oscillator D) :
    oscillatorCoefficient D right (second - chargeNorm D right)
      (oscillatorCoefficient D left (first - chargeNorm D left) polynomial) =
        ∑ᶠ degree : ℕ, (PowerSeries.coeff degree (halfContraction D left right)) •
          commonKernel D left right (first - degree) (second + degree) polynomial := by
  rw [native_ordered_product]
  apply finsum_congr
  intro degree
  rw [common_kernel_branch_exchange]
  rw [show halfContraction D right left = halfContraction D left right by
    simp only [halfContraction, LatticeFiniteNegativeGeneration.bilinear_symmetric D right left]]

def tensorCommonKernel (D : LatticeData) (hu : IsUnit D.G.det) (left right : Charge D)
    (first second : ℤ) : Module.End ℂ (ActualTensor D hu) :=
  TensorProduct.map (commonKernel D left right first second)
    (groundAction D hu left * groundAction D hu right)

theorem tensor_kernel_bounds (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (state : ActualTensor D hu) :
    ∃ firstBound secondBound : ℤ, ∀ first second : ℤ,
      first < firstBound ∨ second < secondBound →
        tensorCommonKernel D hu left right first second state = 0 := by
  induction state using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by intros; simp⟩
  | tmul polynomial vector =>
    obtain ⟨firstBound, secondBound, bound⟩ :=
      common_kernel_rectangular_support D left right polynomial
    refine ⟨firstBound, secondBound, ?_⟩
    intro first second outside
    simp [tensorCommonKernel, TensorProduct.map_tmul, bound first second outside]
  | add firstState secondState firstProof secondProof =>
    obtain ⟨firstLower, firstUpper, firstProof⟩ := firstProof
    obtain ⟨secondLower, secondUpper, secondProof⟩ := secondProof
    refine ⟨min firstLower secondLower, min firstUpper secondUpper, ?_⟩
    intro first second outside
    have firstOutside : first < firstLower ∨ second < firstUpper := by
      rcases outside with outside | outside
      · exact Or.inl (lt_of_lt_of_le outside (min_le_left _ _))
      · exact Or.inr (lt_of_lt_of_le outside (min_le_left _ _))
    have secondOutside : first < secondLower ∨ second < secondUpper := by
      rcases outside with outside | outside
      · exact Or.inl (lt_of_lt_of_le outside (min_le_right _ _))
      · exact Or.inr (lt_of_lt_of_le outside (min_le_right _ _))
    simp [firstProof first second firstOutside, secondProof first second secondOutside]

private def tensorOrderedTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) (state : ActualTensor D hu)
    (degree : ℕ) : ActualTensor D hu :=
  (PowerSeries.coeff degree (halfContraction D left right)) •
    tensorCommonKernel D hu left right (first + degree) (second - degree) state

private theorem tensor_ordered_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) (state : ActualTensor D hu) :
    Function.HasFiniteSupport (tensorOrderedTerm D hu left right first second state) := by
  obtain ⟨firstBound, secondBound, bound⟩ := tensor_kernel_bounds D hu left right state
  apply BddAbove.finite
  refine bddAbove_def.mpr ⟨(second - secondBound).toNat, ?_⟩
  intro degree supported
  by_contra outside
  have zero := bound (first + degree) (second - degree) (Or.inr (by omega))
  exact supported (by simp [tensorOrderedTerm, zero])

private def tensorOrderedExpansion (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) : Module.End ℂ (ActualTensor D hu) where
  toFun state := ∑ᶠ degree : ℕ, tensorOrderedTerm D hu left right first second state degree
  map_add' firstState secondState := by
    have terms : tensorOrderedTerm D hu left right first second (firstState + secondState) =
        fun degree => tensorOrderedTerm D hu left right first second firstState degree +
          tensorOrderedTerm D hu left right first second secondState degree := by
      funext degree
      simp only [tensorOrderedTerm, map_add, smul_add]
    rw [terms]
    exact finsum_add_distrib (tensor_ordered_finite D hu left right first second firstState)
      (tensor_ordered_finite D hu left right first second secondState)
  map_smul' scalar state := by
    have terms : tensorOrderedTerm D hu left right first second (scalar • state) =
        fun degree => scalar • tensorOrderedTerm D hu left right first second state degree := by
      funext degree
      change (PowerSeries.coeff degree (halfContraction D left right)) •
        tensorCommonKernel D hu left right (first + degree) (second - degree) (scalar • state) =
          scalar • ((PowerSeries.coeff degree (halfContraction D left right)) •
            tensorCommonKernel D hu left right (first + degree) (second - degree) state)
      rw [map_smul]
      exact smul_comm _ _ _
    rw [terms]
    exact (smul_finsum' scalar (tensor_ordered_finite D hu left right first second state)).symm

private theorem ground_product_vector (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (vector : ActualGround D hu) :
    groundAction D hu left (groundAction D hu right vector) =
      epsilon D left right • groundAction D hu (left + right) vector := by
  simpa only [Module.End.mul_apply, LinearMap.smul_apply] using
    congrArg (fun operator : Module.End ℂ (ActualGround D hu) => operator vector)
      (ground_action_product D hu left right)

private theorem tensor_ordered_term_pure (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) (polynomial : Oscillator D)
    (vector : ActualGround D hu) (degree : ℕ) :
    tensorOrderedTerm D hu left right first second (polynomial ⊗ₜ[ℂ] vector) degree =
      orderedTerm D left right first second polynomial degree ⊗ₜ[ℂ]
        (epsilon D left right • groundAction D hu (left + right) vector) := by
  simp only [tensorOrderedTerm, tensorCommonKernel, TensorProduct.map_tmul,
    Module.End.mul_apply]
  rw [ground_product_vector]
  rfl

theorem tensor_expansion_pure (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) (polynomial : Oscillator D)
    (vector : ActualGround D hu) :
    tensorOrderedExpansion D hu left right first second (polynomial ⊗ₜ[ℂ] vector) =
      orderedExpansion D left right first second polynomial ⊗ₜ[ℂ]
        groundAction D hu left (groundAction D hu right vector) := by
  have groundProduct := ground_product_vector D hu left right vector
  let tensorMap : Oscillator D →ₗ[ℂ] ActualTensor D hu :=
    (TensorProduct.mk ℂ (Oscillator D) (ActualGround D hu)).flip
    (epsilon D left right • groundAction D hu (left + right) vector)
  have mapped := tensorMap.toAddMonoidHom.map_finsum
    (ordered_finite D left right first second polynomial)
  change (∑ᶠ degree : ℕ,
    tensorOrderedTerm D hu left right first second (polynomial ⊗ₜ[ℂ] vector) degree) = _
  calc
    _ = ∑ᶠ degree : ℕ, tensorMap (orderedTerm D left right first second polynomial degree) :=
      finsum_congr (tensor_ordered_term_pure D hu left right first second polynomial vector)
    _ = tensorMap (∑ᶠ degree : ℕ, orderedTerm D left right first second polynomial degree) :=
      mapped.symm
    _ = _ := by
      rw [groundProduct]
      rfl

theorem charged_tensor_ordered_product (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) (state : ActualTensor D hu) :
    chargedCoefficient D hu left first (chargedCoefficient D hu right second state) =
      (chargeScalar D left * chargeScalar D right) •
        ∑ᶠ degree : ℕ, (PowerSeries.coeff degree (halfContraction D left right)) •
          tensorCommonKernel D hu left right (first + chargeNorm D left + degree)
            (second + chargeNorm D right - degree) state := by
  change _ = (chargeScalar D left * chargeScalar D right) •
    tensorOrderedExpansion D hu left right (first + chargeNorm D left)
      (second + chargeNorm D right) state
  induction state using TensorProduct.induction_on with
  | zero => simp
  | add firstState secondState firstProof secondProof =>
    simp only [map_add, smul_add, firstProof, secondProof]
  | tmul polynomial vector =>
    rw [tensor_expansion_pure]
    have oscillator := native_ordered_product D left right (first + chargeNorm D left)
      (second + chargeNorm D right) polynomial
    simp only [add_sub_cancel_right] at oscillator
    change oscillatorCoefficient D left first (oscillatorCoefficient D right second polynomial) =
      orderedExpansion D left right (first + chargeNorm D left)
        (second + chargeNorm D right) polynomial at oscillator
    simp only [chargedCoefficient, LinearMap.smul_apply, TensorProduct.map_tmul,
      map_smul, smul_smul, oscillator] <;> module

theorem charged_tensor_reverse_ordered_product (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) (state : ActualTensor D hu) :
    chargedCoefficient D hu right second (chargedCoefficient D hu left first state) =
      (chargeScalar D left * chargeScalar D right) •
        ∑ᶠ degree : ℕ, (PowerSeries.coeff degree (halfContraction D left right)) •
          tensorCommonKernel D hu right left (second + chargeNorm D right + degree)
            (first + chargeNorm D left - degree) state := by
  rw [charged_tensor_ordered_product, mul_comm (chargeScalar D right)]
  congr 1
  apply finsum_congr
  intro degree
  rw [show halfContraction D right left = halfContraction D left right by
    simp only [halfContraction, LatticeFiniteNegativeGeneration.bilinear_symmetric D right left]]

end
end D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
