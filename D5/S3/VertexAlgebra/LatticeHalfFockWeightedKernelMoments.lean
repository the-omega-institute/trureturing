/- GID: D5/S3/VertexAlgebra/LatticeHalfFockWeightedKernelMoments
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockWeightedKernelMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Statewise finite binomial moments and their original native creator recurrence. -/

import D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.Binomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockWeightedKernelMoments

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockProductKernel
open LatticeHalfFockOrderedProducts LatticeHalfFock MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

theorem polynomial_weighted_diagonal_finite (D : LatticeData) (left right : Charge D)
    (total shift : ℤ) (polynomial : Oscillator D) (weight : ℤ → ℂ) :
    Function.HasFiniteSupport (fun first : ℤ => weight first •
      commonKernel D left right (first + shift) (total - (first + shift)) polynomial) := by
  obtain ⟨firstBound, secondBound, bound⟩ :=
    common_kernel_rectangular_support D left right polynomial
  apply (Set.finite_Icc (firstBound - shift) (total - secondBound - shift)).subset
  intro first nonzero
  change firstBound - shift ≤ first ∧ first ≤ total - secondBound - shift
  constructor
  · by_contra outside
    exact nonzero (by rw [bound _ _ (Or.inl (by omega)), smul_zero])
  · by_contra outside
    exact nonzero (by rw [bound _ _ (Or.inr (by omega)), smul_zero])

theorem tensor_weighted_diagonal_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (total shift : ℤ) (state : ActualTensor D hu)
    (weight : ℤ → ℂ) : Function.HasFiniteSupport (fun first : ℤ => weight first •
      tensorCommonKernel D hu left right (first + shift) (total - (first + shift)) state) := by
  obtain ⟨firstBound, secondBound, bound⟩ := tensor_kernel_bounds D hu left right state
  apply (Set.finite_Icc (firstBound - shift) (total - secondBound - shift)).subset
  intro first nonzero
  change firstBound - shift ≤ first ∧ first ≤ total - secondBound - shift
  constructor
  · by_contra outside
    exact nonzero (by rw [bound _ _ (Or.inl (by omega)), smul_zero])
  · by_contra outside
    exact nonzero (by rw [bound _ _ (Or.inr (by omega)), smul_zero])

private theorem binomial_shift (first shift : ℤ) (order : ℕ) :
    Ring.choose (((first - shift : ℤ) : ℂ) / 2) order =
      ∑ degree ∈ Finset.range (order + 1),
        Ring.choose (-(shift : ℂ) / 2) degree *
          Ring.choose ((first : ℂ) / 2) (order - degree) := by
  have parameter : (((first - shift : ℤ) : ℂ) / 2) =
      -(shift : ℂ) / 2 + (first : ℂ) / 2 := by push_cast; ring
  rw [parameter, Ring.add_choose_eq order (Commute.all _ _),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private theorem binomial_moment_shift {V : Type*} [AddCommGroup V] [Module ℂ V]
    (value : ℤ → V) (finite : Function.HasFiniteSupport value) (order : ℕ) (shift : ℤ) :
    (∑ᶠ first : ℤ, Ring.choose (((first - shift : ℤ) : ℂ) / 2) order • value first) =
      (∑ᶠ first : ℤ, Ring.choose ((first : ℂ) / 2) order • value first) +
        ∑ degree ∈ Finset.range order, Ring.choose (-(shift : ℂ) / 2) (degree + 1) •
          (∑ᶠ first : ℤ,
            Ring.choose ((first : ℂ) / 2) (order - (degree + 1)) • value first) := by
  classical
  have finiteTerm (degree : ℕ) : Function.HasFiniteSupport (fun first : ℤ =>
      (Ring.choose (-(shift : ℂ) / 2) degree *
        Ring.choose ((first : ℂ) / 2) (order - degree)) • value first) := by
    apply finite.subset
    intro first nonzero zero
    exact nonzero (by rw [zero, smul_zero])
  calc
    _ = ∑ᶠ first : ℤ, ∑ degree ∈ Finset.range (order + 1),
        (Ring.choose (-(shift : ℂ) / 2) degree *
          Ring.choose ((first : ℂ) / 2) (order - degree)) • value first := by
      apply finsum_congr
      intro first
      rw [binomial_shift, Finset.sum_smul]
    _ = ∑ degree ∈ Finset.range (order + 1), ∑ᶠ first : ℤ,
        (Ring.choose (-(shift : ℂ) / 2) degree *
          Ring.choose ((first : ℂ) / 2) (order - degree)) • value first :=
      finsum_sum_comm _ _ (fun degree _ => finiteTerm degree)
    _ = ∑ degree ∈ Finset.range (order + 1),
        Ring.choose (-(shift : ℂ) / 2) degree •
          (∑ᶠ first : ℤ, Ring.choose ((first : ℂ) / 2) (order - degree) • value first) := by
      apply Finset.sum_congr rfl
      intro degree member
      simp only [mul_smul]
      exact (smul_finsum' _ (Function.HasFiniteSupport.smul_right
        (fun first : ℤ => Ring.choose ((first : ℂ) / 2) (order - degree)) finite)).symm
    _ = _ := by
      rw [Finset.sum_range_succ']
      simp only [Ring.choose_zero_right, one_smul, Nat.sub_zero]
      exact add_comm _ _

/-- A polynomial moment is summed only after applying the original kernel to its input. -/
def polynomialMoment (D : LatticeData) (left right : Charge D) (order : ℕ) (total : ℤ) :
    Module.End ℂ (Oscillator D) where
  toFun polynomial := ∑ᶠ first : ℤ, Ring.choose ((first : ℂ) / 2) order •
    commonKernel D left right first (total - first) polynomial
  map_add' firstPolynomial secondPolynomial := by
    simp only [map_add, smul_add]
    exact finsum_add_distrib
      (by simpa only [add_zero] using polynomial_weighted_diagonal_finite
        D left right total 0 firstPolynomial (fun first => Ring.choose ((first : ℂ) / 2) order))
      (by simpa only [add_zero] using polynomial_weighted_diagonal_finite
        D left right total 0 secondPolynomial (fun first => Ring.choose ((first : ℂ) / 2) order))
  map_smul' scalar polynomial := by
    simp only [map_smul, RingHom.id_apply]
    simp only [smul_comm (Ring.choose _ order) scalar]
    exact (smul_finsum' scalar (by simpa only [add_zero] using
      polynomial_weighted_diagonal_finite D left right total 0 polynomial
        (fun first => Ring.choose ((first : ℂ) / 2) order))).symm

/-- The native moment retains the original ordered ground actions in `tensorCommonKernel`. -/
def tensorMoment (D : LatticeData) (hu : IsUnit D.G.det) (left right : Charge D)
    (order : ℕ) (total : ℤ) : Module.End ℂ (ActualTensor D hu) where
  toFun state := ∑ᶠ first : ℤ, Ring.choose ((first : ℂ) / 2) order •
    tensorCommonKernel D hu left right first (total - first) state
  map_add' firstState secondState := by
    simp only [map_add, smul_add]
    exact finsum_add_distrib
      (by simpa only [add_zero] using tensor_weighted_diagonal_finite
        D hu left right total 0 firstState (fun first => Ring.choose ((first : ℂ) / 2) order))
      (by simpa only [add_zero] using tensor_weighted_diagonal_finite
        D hu left right total 0 secondState (fun first => Ring.choose ((first : ℂ) / 2) order))
  map_smul' scalar state := by
    simp only [map_smul, RingHom.id_apply]
    simp only [smul_comm (Ring.choose _ order) scalar]
    exact (smul_finsum' scalar (by simpa only [add_zero] using
      tensor_weighted_diagonal_finite D hu left right total 0 state
        (fun first => Ring.choose ((first : ℂ) / 2) order))).symm

private theorem shifted_polynomial_moment (D : LatticeData) (left right : Charge D)
    (order : ℕ) (total shift : ℤ) (polynomial : Oscillator D) :
    (∑ᶠ first : ℤ, Ring.choose ((first : ℂ) / 2) order •
      commonKernel D left right (first + shift) (total - first) polynomial) =
      polynomialMoment D left right order (total + shift) polynomial +
        ∑ degree ∈ Finset.range order, Ring.choose (-(shift : ℂ) / 2) (degree + 1) •
          polynomialMoment D left right (order - (degree + 1)) (total + shift) polynomial := by
  have finite : Function.HasFiniteSupport (fun first : ℤ =>
      commonKernel D left right first (total + shift - first) polynomial) := by
    simpa only [add_zero, one_smul] using polynomial_weighted_diagonal_finite
      D left right (total + shift) 0 polynomial (fun _ => 1)
  calc
    _ = ∑ᶠ first : ℤ, Ring.choose (((first - shift : ℤ) : ℂ) / 2) order •
        commonKernel D left right first (total + shift - first) polynomial := by
      apply finsum_eq_of_bijective (Equiv.addRight shift) (Equiv.addRight shift).bijective
      intro first
      change _ = Ring.choose (((first + shift - shift : ℤ) : ℂ) / 2) order •
        commonKernel D left right (first + shift) (total + shift - (first + shift)) polynomial
      rw [add_sub_cancel_right, show total + shift - (first + shift) = total - first by omega]
    _ = _ := binomial_moment_shift _ finite order shift

theorem polynomial_moment_creator (D : LatticeData) (left right : Charge D)
    (order : ℕ) (total : ℤ) (polynomial : Oscillator D) (index : Index D) :
    polynomialMoment D left right order total (X index * polynomial) =
      X index * polynomialMoment D left right order total polynomial -
        (bilinear D (left + right) (unitCharge D index.1) : ℂ) •
          polynomialMoment D left right order (total + omega D index) polynomial -
        (bilinear D left (unitCharge D index.1) : ℂ) •
          ∑ degree ∈ Finset.range order,
            Ring.choose (-(omega D index : ℂ) / 2) (degree + 1) •
              polynomialMoment D left right (order - (degree + 1))
                (total + omega D index) polynomial := by
  classical
  let weight : ℤ → ℂ := fun first => Ring.choose ((first : ℂ) / 2) order
  let leftScalar : ℂ := bilinear D left (unitCharge D index.1)
  let rightScalar : ℂ := bilinear D right (unitCharge D index.1)
  let main : ℤ → Oscillator D := fun first => X index *
    (weight first • commonKernel D left right first (total - first) polynomial)
  let leftTerm : ℤ → Oscillator D := fun first => leftScalar •
    (weight first • commonKernel D left right (first + omega D index) (total - first) polynomial)
  let rightTerm : ℤ → Oscillator D := fun first => rightScalar •
    (weight first • commonKernel D left right first (total + omega D index - first) polynomial)
  have mainBase : Function.HasFiniteSupport (fun first : ℤ => weight first •
      commonKernel D left right first (total - first) polynomial) := by
    simpa only [add_zero] using
      polynomial_weighted_diagonal_finite D left right total 0 polynomial weight
  have leftBase : Function.HasFiniteSupport (fun first : ℤ => weight first •
      commonKernel D left right (first + omega D index) (total - first) polynomial) := by
    have finite := polynomial_weighted_diagonal_finite D left right
      (total + omega D index) (omega D index) polynomial weight
    have diagonal (first : ℤ) :
        total + omega D index - (first + omega D index) = total - first := by omega
    simpa only [diagonal] using finite
  have rightBase : Function.HasFiniteSupport (fun first : ℤ => weight first •
      commonKernel D left right first (total + omega D index - first) polynomial) := by
    simpa only [add_zero] using polynomial_weighted_diagonal_finite
      D left right (total + omega D index) 0 polynomial weight
  have mainFinite : Function.HasFiniteSupport main :=
    mainBase.fun_comp (show X index * (0 : Oscillator D) = 0 by simp)
  have leftFinite : Function.HasFiniteSupport leftTerm :=
    leftBase.fun_comp (show leftScalar • (0 : Oscillator D) = 0 by simp)
  have rightFinite : Function.HasFiniteSupport rightTerm :=
    rightBase.fun_comp (show rightScalar • (0 : Oscillator D) = 0 by simp)
  have distribution : polynomialMoment D left right order total (X index * polynomial) =
      X index * polynomialMoment D left right order total polynomial -
        leftScalar • (∑ᶠ first : ℤ, weight first •
          commonKernel D left right (first + omega D index) (total - first) polynomial) -
        rightScalar • polynomialMoment D left right order (total + omega D index) polynomial := by
    calc
      _ = ∑ᶠ first : ℤ, (main first - leftTerm first) - rightTerm first := by
        apply finsum_congr
        intro first
        dsimp only [main, leftTerm, rightTerm, leftScalar, rightScalar, weight]
        rw [kernel_creator]
        rw [show total - first + omega D index = total + omega D index - first by omega]
        simp only [smul_sub, ← mul_smul_comm, smul_comm]
      _ = (∑ᶠ first : ℤ, main first) - (∑ᶠ first : ℤ, leftTerm first) -
          (∑ᶠ first : ℤ, rightTerm first) := by
        rw [finsum_sub_distrib (mainFinite.sub leftFinite) rightFinite,
          finsum_sub_distrib mainFinite leftFinite]
      _ = _ := by
        change (∑ᶠ first : ℤ, X index * (weight first •
            commonKernel D left right first (total - first) polynomial)) -
          (∑ᶠ first : ℤ, leftScalar • (weight first •
            commonKernel D left right (first + omega D index) (total - first) polynomial)) -
          (∑ᶠ first : ℤ, rightScalar • (weight first •
            commonKernel D left right first (total + omega D index - first) polynomial)) = _
        rw [← mul_finsum' _ _ mainBase, ← smul_finsum' _ leftBase,
          ← smul_finsum' _ rightBase]
        rfl
  rw [distribution]
  have shifted := shifted_polynomial_moment D left right order total
    (omega D index : ℤ) polynomial
  simp only [Int.cast_natCast] at shifted
  change _ - leftScalar • (∑ᶠ first : ℤ, Ring.choose ((first : ℂ) / 2) order •
    commonKernel D left right (first + omega D index) (total - first) polynomial) - _ = _
  rw [shifted]
  have gram : (bilinear D (left + right) (unitCharge D index.1) : ℂ) =
      leftScalar + rightScalar := by
    simp only [leftScalar, rightScalar]
    have integral : bilinear D (left + right) (unitCharge D index.1) =
        bilinear D left (unitCharge D index.1) +
          bilinear D right (unitCharge D index.1) := by
      simp [bilinear, add_mul, Finset.sum_add_distrib]
    rw [integral, Int.cast_add]
  rw [gram]
  module

theorem tensor_moment_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (order : ℕ) (total : ℤ)
    (polynomial : Oscillator D) (vector : ActualGround D hu) :
    tensorMoment D hu left right order total (polynomial ⊗ₜ[ℂ] vector) =
      polynomialMoment D left right order total polynomial ⊗ₜ[ℂ]
        (groundAction D hu left * groundAction D hu right) vector := by
  let groundValue := (groundAction D hu left * groundAction D hu right) vector
  let lift := (TensorProduct.mk ℂ (Oscillator D) (ActualGround D hu)).flip groundValue
  have finite : Function.HasFiniteSupport (fun first : ℤ =>
      Ring.choose ((first : ℂ) / 2) order •
        commonKernel D left right first (total - first) polynomial) := by
    simpa only [add_zero] using polynomial_weighted_diagonal_finite
      D left right total 0 polynomial (fun first => Ring.choose ((first : ℂ) / 2) order)
  have transported := lift.toAddMonoidHom.map_finsum finite
  change ((∑ᶠ first : ℤ, Ring.choose ((first : ℂ) / 2) order •
      commonKernel D left right first (total - first) polynomial) ⊗ₜ[ℂ] groundValue) =
    ∑ᶠ first : ℤ, (Ring.choose ((first : ℂ) / 2) order •
      commonKernel D left right first (total - first) polynomial) ⊗ₜ[ℂ] groundValue at transported
  change (∑ᶠ first : ℤ, Ring.choose ((first : ℂ) / 2) order •
      tensorCommonKernel D hu left right first (total - first) (polynomial ⊗ₜ[ℂ] vector)) = _
  simpa only [tensorCommonKernel, TensorProduct.map_tmul, TensorProduct.smul_tmul']
    using transported.symm

theorem tensor_moment_creator (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (order : ℕ) (total : ℤ)
    (state : ActualTensor D hu) (index : Index D) :
    tensorMoment D hu left right order total
        (tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1) state) =
      tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1)
        (tensorMoment D hu left right order total state) -
      (bilinear D (left + right) (unitCharge D index.1) : ℂ) •
        tensorMoment D hu left right order (total + omega D index) state -
      (bilinear D left (unitCharge D index.1) : ℂ) •
        ∑ degree ∈ Finset.range order,
          Ring.choose (-(omega D index : ℂ) / 2) (degree + 1) •
            tensorMoment D hu left right (order - (degree + 1))
              (total + omega D index) state := by
  classical
  let creator := tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1)
  have operators : tensorMoment D hu left right order total * creator =
      creator * tensorMoment D hu left right order total -
      (bilinear D (left + right) (unitCharge D index.1) : ℂ) •
        tensorMoment D hu left right order (total + omega D index) -
      (bilinear D left (unitCharge D index.1) : ℂ) •
        ∑ degree ∈ Finset.range order,
          Ring.choose (-(omega D index : ℂ) / 2) (degree + 1) •
            tensorMoment D hu left right (order - (degree + 1)) (total + omega D index) := by
    apply TensorProduct.ext'
    intro polynomial vector
    simpa only [creator, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.sum_apply, tensorCurrent, tensorEnd,
      TensorProduct.map_tmul, LinearMap.id_apply, current_negative,
      LinearMap.mulLeft_apply, tensor_moment_tmul, TensorProduct.sub_tmul,
      ← TensorProduct.smul_tmul', TensorProduct.sum_tmul] using
      congrArg (fun value : Oscillator D => value ⊗ₜ[ℂ]
        (groundAction D hu left * groundAction D hu right) vector)
        (polynomial_moment_creator D left right order total polynomial index)
  simpa only [creator, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.sum_apply] using
    congrArg (fun operator : Module.End ℂ (ActualTensor D hu) => operator state) operators

end
end D5.S3.VertexAlgebra.LatticeHalfFockWeightedKernelMoments
