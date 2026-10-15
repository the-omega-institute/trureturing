/- GID: D5/S3/VertexAlgebra/LatticeHalfFockProductKernel
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockProductKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native odd-frequency bivariate creation kernels have rectangular support. -/

import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
import D5.S3.VertexAlgebra.LatticeActualProductKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockProductKernel

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients MvPolynomial
open LatticeActualProductKernel
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
  bivariateCoefficientConvolution (halfCreationCoeff D left) (halfCreationCoeff D right)
    first second

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
  first
  | rfl
  | simp [pairConvolution, bivariateCoefficientConvolution, Finsupp.sum]

private theorem convolution_monomial (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (exponent : Fin 2 →₀ ℕ) (coefficient : Oscillator D) :
    pairConvolution D left right first second (monomial exponent coefficient) =
      coefficient * (halfCreationCoeff D left (first + exponent 0) *
        halfCreationCoeff D right (second + exponent 1)) := by
  exact bivariateCoefficientConvolution_monomial _ _ _ _ _ _

private theorem convolution_C_mul (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (coefficient : Oscillator D) (polynomial : PairPolynomial D) :
    pairConvolution D left right first second (C coefficient * polynomial) =
      coefficient * pairConvolution D left right first second polynomial := by
  exact bivariateCoefficientConvolution_C_mul _ _ _ _ _ _

private theorem convolution_X_zero (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (degree : ℕ) (polynomial : PairPolynomial D) :
    pairConvolution D left right first second (X 0 ^ degree * polynomial) =
      pairConvolution D left right (first + degree) second polynomial := by
  exact bivariateCoefficientConvolution_X_zero _ _ _ _ _ _

private theorem convolution_X_one (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (degree : ℕ) (polynomial : PairPolynomial D) :
    pairConvolution D left right first second (X 1 ^ degree * polynomial) =
      pairConvolution D left right first (second + degree) polynomial := by
  exact bivariateCoefficientConvolution_X_one _ _ _ _ _ _

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

theorem common_kernel_branch_exchange (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (polynomial : Oscillator D) :
    commonKernel D left right first second polynomial =
      commonKernel D right left second first polynomial := by
  classical
  induction polynomial using MvPolynomial.induction_on generalizing first second with
  | C scalar => simp only [kernel_constant]; ring
  | add firstPolynomial secondPolynomial firstProof secondProof =>
    simp only [map_add, firstProof, secondProof]
  | mul_X polynomial index inductionProof =>
    simp only [mul_comm polynomial (X index)]
    rw [kernel_creator, kernel_creator]
    rw [inductionProof, inductionProof, inductionProof]
    module

end
end D5.S3.VertexAlgebra.LatticeHalfFockProductKernel
