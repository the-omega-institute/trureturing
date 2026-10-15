/- GID: D5/S3/VertexAlgebra/LatticeHalfFockDiagonalFusion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockDiagonalFusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual polynomial diagonal fusion of the native half-lattice product kernel. -/

import D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockDiagonalFusion

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockProductKernel
open LatticeHalfFockOrderedProducts LatticeHalfFockGroundProducts
open LatticeActualProductKernel MvPolynomial
open scoped BigOperators TensorProduct

macro "originalCreationSupplier% " supplier:ident : term => do
  let suffix := supplier.getId.toString
  unless suffix ∈ ["exponential_derivative", "solution_unique"] do
    Lean.Macro.throwError "unknown original creation supplier"
  let components := ["D5", "S3", "VertexAlgebra", "LatticeHalfFockChargedCoefficients"]
  let privatePrefix := components.foldl Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private")
  let scopedName := components.foldl Lean.Name.str (Lean.Name.num privatePrefix 0)
  return Lean.mkIdent (Lean.Name.str scopedName suffix)

noncomputable section

private theorem creation_series_add (D : LatticeData) (left right : Charge D) :
    halfCreationSeries D (left + right) =
      halfCreationSeries D left + halfCreationSeries D right := by
  apply PowerSeries.ext
  intro degree
  simp only [halfCreationSeries, PowerSeries.coeff_mk, map_add]
  split_ifs with odd
  · simp only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib, smul_add]
  · simp

private theorem creation_derivative (D : LatticeData) (charge : Charge D) :
    PowerSeries.derivative (Oscillator D) (halfCreationExponential D charge) =
      halfCreationExponential D charge *
        PowerSeries.derivative (Oscillator D) (halfCreationSeries D charge) := by
  exact LatticeHalfFockChargedCoefficients.exponential_derivative D charge

theorem creation_exponential_add (D : LatticeData) (left right : Charge D) :
    halfCreationExponential D (left + right) =
      halfCreationExponential D left * halfCreationExponential D right := by
  let first := halfCreationExponential D (left + right)
  let second := halfCreationExponential D left * halfCreationExponential D right
  let driver := PowerSeries.derivative (Oscillator D) (halfCreationSeries D (left + right))
  have firstEquation : PowerSeries.derivative (Oscillator D) first = first * driver :=
    creation_derivative D (left + right)
  have secondEquation : PowerSeries.derivative (Oscillator D) second = second * driver := by
    dsimp [second, driver]
    rw [(PowerSeries.derivative (Oscillator D)).leibniz, creation_derivative,
      creation_derivative, creation_series_add, map_add]
    ring
  exact (originalCreationSupplier% solution_unique) first second driver
    firstEquation secondEquation (by
      simp [first, second, PowerSeries.coeff_mul, exponential_constant])

private theorem creation_pair_support (D : LatticeData) (left right : Charge D)
    (total : ℤ) : Function.support (fun first : ℤ =>
      halfCreationCoeff D left first * halfCreationCoeff D right (total - first)) ⊆
        (Finset.Icc 0 total : Finset ℤ) := by
  intro first nonzero
  simp only [Finset.mem_coe, Finset.mem_Icc]
  constructor
  · by_contra negative
    exact nonzero (by simp [halfCreationCoeff, show first < 0 by omega])
  · by_contra negative
    exact nonzero (by simp [halfCreationCoeff, show total - first < 0 by omega])

theorem creation_coefficient_add (D : LatticeData) (left right : Charge D) (total : ℤ) :
    (∑ᶠ first : ℤ, halfCreationCoeff D left first *
      halfCreationCoeff D right (total - first)) = halfCreationCoeff D (left + right) total := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (creation_pair_support D left right total)]
  by_cases negative : total < 0
  · have empty : (Finset.Icc 0 total : Finset ℤ) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro first member
      have := Finset.mem_Icc.mp member
      omega
    simp [empty, halfCreationCoeff, negative]
  · rw [halfCreationCoeff, if_neg negative, creation_exponential_add,
      PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_bij (fun first _ => first.toNat)
    · intro first member
      have := Finset.mem_Icc.mp member
      simp only [Finset.mem_range]
      omega
    · intro first firstMember second secondMember equal
      have := Finset.mem_Icc.mp firstMember
      have := Finset.mem_Icc.mp secondMember
      omega
    · intro degree member
      refine ⟨(degree : ℤ), ?_, by simp⟩
      simp only [Finset.mem_Icc]
      have := Finset.mem_range.mp member
      omega
    · intro first member
      have bounds := Finset.mem_Icc.mp member
      simp only [halfCreationCoeff, if_neg (by omega : ¬ first < 0),
        if_neg (by omega : ¬ total - first < 0)]
      rw [show (total - first).toNat = total.toNat - first.toNat by omega]

private theorem kernel_diagonal_finite (D : LatticeData) (left right : Charge D)
    (total shift : ℤ) (polynomial : Oscillator D) : Function.HasFiniteSupport
      (fun first : ℤ => commonKernel D left right (first + shift)
        (total - (first + shift)) polynomial) := by
  obtain ⟨firstBound, secondBound, bound⟩ :=
    common_kernel_rectangular_support D left right polynomial
  apply (Set.finite_Icc (firstBound - shift) (total - secondBound - shift)).subset
  intro first nonzero
  change firstBound - shift ≤ first ∧ first ≤ total - secondBound - shift
  constructor
  · by_contra outside
    exact nonzero (bound _ _ (Or.inl (by omega)))
  · by_contra outside
    exact nonzero (bound _ _ (Or.inr (by omega)))

private theorem fused_creator (D : LatticeData) (charge : Charge D)
    (total : ℤ) (polynomial : Oscillator D) (index : Index D) :
    coefficientConvolution (halfCreationCoeff D charge) total
        (halfTranslatedPolynomial D charge (X index * polynomial)) =
      X index * coefficientConvolution (halfCreationCoeff D charge) total
          (halfTranslatedPolynomial D charge polynomial) -
        (bilinear D charge (unitCharge D index.1) : ℂ) •
          coefficientConvolution (halfCreationCoeff D charge) (total + omega D index)
            (halfTranslatedPolynomial D charge polynomial) := by
  simp only [halfTranslatedPolynomial, map_mul, MvPolynomial.eval₂AlgHom_X,
    halfTranslationVariable, sub_mul, map_sub]
  rw [coefficientConvolution_C_mul]
  rw [mul_assoc, coefficientConvolution_C_mul]
  rw [coefficientConvolution_X_pow]
  rw [smul_mul_assoc, one_mul]

theorem common_kernel_diagonal_fusion (D : LatticeData) (left right : Charge D)
    (total : ℤ) (polynomial : Oscillator D) :
    (∑ᶠ first : ℤ, commonKernel D left right first (total - first) polynomial) =
      coefficientConvolution (halfCreationCoeff D (left + right)) total
        (halfTranslatedPolynomial D (left + right) polynomial) := by
  classical
  induction polynomial using MvPolynomial.induction_on generalizing total with
  | C scalar =>
    simp only [kernel_constant]
    rw [← mul_finsum, creation_coefficient_add]
    have translated : halfTranslatedPolynomial D (left + right) (C scalar) =
        Polynomial.C (C scalar) := by simp [halfTranslatedPolynomial]
    rw [translated]
    simpa only [Nat.cast_zero, add_zero, Polynomial.monomial_zero_left] using
      (coefficientConvolution_monomial (halfCreationCoeff D (left + right)) total 0 (C scalar)).symm
  | add firstPolynomial secondPolynomial firstProof secondProof =>
    simp only [map_add, halfTranslatedPolynomial]
    rw [finsum_add_distrib
      (by simpa using kernel_diagonal_finite D left right total 0 firstPolynomial)
      (by simpa using kernel_diagonal_finite D left right total 0 secondPolynomial)]
    exact congrArg₂ (· + ·) (firstProof total) (secondProof total)
  | mul_X polynomial index inductionProof =>
    simp only [mul_comm polynomial (X index), LatticeHalfFockProductKernel.kernel_creator]
    have firstFinite := kernel_diagonal_finite D left right total 0 polynomial
    have leftFinite := kernel_diagonal_finite D left right (total + omega D index)
      (omega D index) polynomial
    have rightFinite := kernel_diagonal_finite D left right (total + omega D index) 0 polynomial
    simp only [add_zero] at firstFinite rightFinite
    have leftRewrite : (fun first : ℤ =>
        commonKernel D left right (first + omega D index) (total - first) polynomial) =
        fun first => commonKernel D left right (first + omega D index)
          (total + omega D index - (first + omega D index)) polynomial := by
      funext first
      congr 2
      omega
    have rightRewrite : (fun first : ℤ =>
        commonKernel D left right first (total - first + omega D index) polynomial) =
        fun first => commonKernel D left right first (total + omega D index - first) polynomial := by
      funext first
      congr 2
      omega
    have leftOriginal : Function.HasFiniteSupport (fun first : ℤ =>
        commonKernel D left right (first + omega D index) (total - first) polynomial) := by
      rw [leftRewrite]
      exact leftFinite
    have rightOriginal : Function.HasFiniteSupport (fun first : ℤ =>
        commonKernel D left right first (total - first + omega D index) polynomial) := by
      rw [rightRewrite]
      exact rightFinite
    have multiplied : Function.HasFiniteSupport (fun first : ℤ =>
        X index * commonKernel D left right first (total - first) polynomial) := by
      apply firstFinite.subset
      intro first nonzero zero
      dsimp only at zero ⊢
      exact nonzero (by simp only [zero, mul_zero])
    have leftScaled : Function.HasFiniteSupport (fun first : ℤ =>
        (bilinear D left (unitCharge D index.1) : ℂ) •
          commonKernel D left right (first + omega D index) (total - first) polynomial) := by
      apply leftOriginal.subset
      intro first nonzero zero
      dsimp only at zero ⊢
      exact nonzero (by simp only [zero, smul_zero])
    have rightScaled : Function.HasFiniteSupport (fun first : ℤ =>
        (bilinear D right (unitCharge D index.1) : ℂ) •
          commonKernel D left right first (total - first + omega D index) polynomial) := by
      apply rightOriginal.subset
      intro first nonzero zero
      dsimp only at zero ⊢
      exact nonzero (by simp only [zero, smul_zero])
    have firstDistribution := finsum_sub_distrib (multiplied.sub leftScaled) rightScaled
    have secondDistribution := finsum_sub_distrib multiplied leftScaled
    simp only [Pi.sub_apply] at firstDistribution secondDistribution
    rw [firstDistribution, secondDistribution]
    rw [← mul_finsum, ← smul_finsum' _ leftOriginal, ← smul_finsum' _ rightOriginal,
      leftRewrite, rightRewrite]
    have reindex : (∑ᶠ first : ℤ, commonKernel D left right (first + omega D index)
        (total + omega D index - (first + omega D index)) polynomial) =
        ∑ᶠ first : ℤ, commonKernel D left right first
          (total + omega D index - first) polynomial := by
      apply finsum_eq_of_bijective (Equiv.addRight (omega D index : ℤ))
        (Equiv.addRight (omega D index : ℤ)).bijective
      intro first
      rfl
    rw [reindex, inductionProof, inductionProof, fused_creator]
    have gram : bilinear D (left + right) (unitCharge D index.1) =
        bilinear D left (unitCharge D index.1) + bilinear D right (unitCharge D index.1) := by
      simp [bilinear, add_mul, Finset.sum_add_distrib]
    rw [gram, Int.cast_add, add_smul]
    module

private theorem tensor_diagonal_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (total : ℤ) (state : ActualTensor D hu) :
    Function.HasFiniteSupport (fun first : ℤ =>
      tensorCommonKernel D hu left right first (total - first) state) := by
  obtain ⟨firstBound, secondBound, bound⟩ := tensor_kernel_bounds D hu left right state
  apply (Set.finite_Icc firstBound (total - secondBound)).subset
  intro first nonzero
  change firstBound ≤ first ∧ first ≤ total - secondBound
  constructor
  · by_contra outside
    exact nonzero (bound _ _ (Or.inl (by omega)))
  · by_contra outside
    exact nonzero (bound _ _ (Or.inr (by omega)))

theorem tensor_common_kernel_diagonal_fusion (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (total : ℤ) (state : ActualTensor D hu) :
    (∑ᶠ first : ℤ, tensorCommonKernel D hu left right first (total - first) state) =
      epsilon D left right • TensorProduct.map
        (oscillatorCoefficient D (left + right) (total - chargeNorm D (left + right)))
        (groundAction D hu (left + right)) state := by
  classical
  induction state using TensorProduct.induction_on with
  | zero => simp
  | tmul polynomial vector =>
    let groundValue := (groundAction D hu left * groundAction D hu right) vector
    let tensorMap := (TensorProduct.mk ℂ (Oscillator D) (ActualGround D hu)).flip groundValue
    have finite := kernel_diagonal_finite D left right total 0 polynomial
    simp only [add_zero] at finite
    have summed :
        (∑ᶠ first : ℤ, commonKernel D left right first (total - first) polynomial) ⊗ₜ[ℂ]
            groundValue =
          ∑ᶠ first : ℤ, commonKernel D left right first (total - first) polynomial ⊗ₜ[ℂ]
            groundValue := tensorMap.toAddMonoidHom.map_finsum finite
    change (∑ᶠ first : ℤ, commonKernel D left right first (total - first) polynomial ⊗ₜ[ℂ]
      groundValue) = _
    rw [← summed, common_kernel_diagonal_fusion]
    have native : coefficientConvolution (halfCreationCoeff D (left + right)) total
        (halfTranslatedPolynomial D (left + right) polynomial) =
        oscillatorCoefficient D (left + right) (total - chargeNorm D (left + right))
          polynomial := by
      change _ = ∑ᶠ degree : ℕ,
        oscillatorTerm D (left + right) (total - chargeNorm D (left + right)) polynomial degree
      rw [finsum_eq_sum_of_support_subset _
        (term_support D (left + right) (total - chargeNorm D (left + right)) polynomial),
        coefficientConvolution_expansion]
      apply Finset.sum_congr rfl
      intro degree member
      simp only [oscillatorTerm]
      congr 2
      omega
    rw [native]
    change _ ⊗ₜ[ℂ] ((groundAction D hu left * groundAction D hu right) vector) = _
    rw [ground_action_product]
    simp only [LinearMap.smul_apply, TensorProduct.tmul_smul, TensorProduct.map_tmul]
  | add firstState secondState firstProof secondProof =>
    simp only [map_add]
    rw [finsum_add_distrib (tensor_diagonal_finite D hu left right total firstState)
      (tensor_diagonal_finite D hu left right total secondState), firstProof, secondProof]
    exact (smul_add _ _ _).symm

end
end D5.S3.VertexAlgebra.LatticeHalfFockDiagonalFusion
