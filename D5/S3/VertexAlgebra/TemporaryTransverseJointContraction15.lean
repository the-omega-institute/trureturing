import D5.S3.VertexAlgebra.TemporaryTransverseJointContraction14
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic

set_option autoImplicit false

open scoped Classical

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
  LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

def transverseEpsilonSpace (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank) :
    Submodule ℂ (State D) :=
  Submodule.span ℂ {state | ∃ (charge : Charge D) (powers : Index D →₀ ℕ) (subset : Finset ℕ),
    (∀ frequency : ℕ, powers (xAxis, frequency) = 0) ∧
    (∀ frequency : ℕ, powers (yAxis, frequency) = 0) ∧ subset ⊆ {3} ∧
    state = nativeState D frame charge powers 1 subset}


section Spectrum

variable (D : LatticeData) (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
  (xAxis yAxis : Fin D.rank)

local notation "nativeBasis" => nativeCoefficientBasis D frame inverse leftFrameInverse rightFrameInverse
local notation "inverseK" => Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
local notation "projector" => P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis

theorem native_P_range_coefficients (state : State D) :
    state ∈ LinearMap.range projector ↔
      ∀ index : NativeCoefficientIndex D, nativeOccupation D xAxis yAxis index ≠ 0 →
        (nativeBasis).repr state index = 0 := by
  constructor
  · rintro ⟨preimage, rfl⟩ index nonzero
    simp only [P, coefficientDiagonal_repr, if_neg nonzero, zero_mul]
  · intro supported
    refine ⟨state, ?_⟩
    apply (nativeBasis).ext_elem
    intro index
    simp only [P, coefficientDiagonal_repr]
    by_cases zero : nativeOccupation D xAxis yAxis index = 0
    · simp [zero]
    · simp [zero, supported index zero]

theorem native_P_range_transverse_epsilon :
    LinearMap.range projector = transverseEpsilonSpace D frame xAxis yAxis := by
  apply le_antisymm
  · rw [P, coefficientDiagonal, Module.Basis.constr_range]
    apply Submodule.span_le.mpr
    rintro state ⟨index, rfl⟩
    dsimp only
    by_cases zero : nativeOccupation D xAxis yAxis index = 0
    · rw [if_pos zero, one_smul, nativeCoefficientBasis_as_signed]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      have characterization := (kappa_zero_iff D xAxis yAxis index.1.2 (toggleOne index.2)).mp zero
      exact ⟨index.1.1, index.1.2, toggleOne index.2,
        characterization.1, characterization.2.1, characterization.2.2, rfl⟩
    · simp only [if_neg zero, zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro state ⟨charge, powers, subset, xZero, yZero, onlyEpsilon, rfl⟩
    refine ⟨nativeState D frame charge powers 1 subset, ?_⟩
    rw [P_native, if_pos ((kappa_zero_iff D xAxis yAxis powers subset).mpr
      ⟨xZero, yZero, onlyEpsilon⟩), one_smul]

variable
  (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
  (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)

local notation "originalK" => K D (frame xAxis) (frame yAxis) (Eq.trans (xDual xAxis) (if_pos (Eq.refl xAxis)))

include yDual in
theorem native_inverse_projection_on_K_eigenvector (count : ℕ) (state : State D)
    (eigenvector : originalK state = (count : ℂ) • state) :
    inverseK state = (count : ℂ)⁻¹ • state ∧
      projector state = (if count = 0 then 1 else 0 : ℂ) • state := by
  have coefficients (index : NativeCoefficientIndex D) :
      (nativeOccupation D xAxis yAxis index : ℂ) * (nativeBasis).repr state index =
        (count : ℂ) * (nativeBasis).repr state index := by
    have equality := congrArg (fun vector : State D => (nativeBasis).repr vector index) eigenvector
    simpa only [original_K_repr D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis xDual yDual,
      map_smul, Finsupp.smul_apply, smul_eq_mul] using equality
  have outsideZero (index : NativeCoefficientIndex D)
      (different : nativeOccupation D xAxis yAxis index ≠ count) : (nativeBasis).repr state index = 0 := by
    by_contra nonzero
    have equalCasts := mul_right_cancel₀ nonzero (coefficients index)
    exact different (by exact_mod_cast equalCasts)
  constructor
  · apply (nativeBasis).ext_elem
    intro index
    simp only [Kdagger, coefficientDiagonal_repr, map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases same : nativeOccupation D xAxis yAxis index = count
    · rw [same]
    · simp [outsideZero index same]
  · apply (nativeBasis).ext_elem
    intro index
    simp only [P, coefficientDiagonal_repr, map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases same : nativeOccupation D xAxis yAxis index = count
    · rw [same]
    · simp [outsideZero index same]

include yDual in
theorem native_commutations_of_K_commutation (operator : Module.End ℂ (State D))
    (commutes : originalK * operator = operator * originalK) :
    operator * inverseK = inverseK * operator ∧ operator * projector = projector * operator := by
  have images (index : NativeCoefficientIndex D) :
      originalK (operator (nativeBasis index)) =
        (nativeOccupation D xAxis yAxis index : ℂ) • operator (nativeBasis index) := by
    have equality := congrArg (fun endomorphism : Module.End ℂ (State D) =>
      endomorphism (nativeBasis index)) commutes
    simpa only [Module.End.mul_apply,
      original_K_coefficient_basis D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis xDual yDual,
      map_smul] using equality
  constructor
  · apply (nativeBasis).ext
    intro index
    have action := (native_inverse_projection_on_K_eigenvector D frame inverse leftFrameInverse
      rightFrameInverse xAxis yAxis xDual yDual _ _ (images index)).1
    simpa only [Module.End.mul_apply, Kdagger_basis, map_smul] using action.symm
  · apply (nativeBasis).ext
    intro index
    have action := (native_inverse_projection_on_K_eigenvector D frame inverse leftFrameInverse
      rightFrameInverse xAxis yAxis xDual yDual _ _ (images index)).2
    simpa only [Module.End.mul_apply, P_basis, map_smul] using action.symm

include inverse leftFrameInverse rightFrameInverse yDual in
theorem original_K_kernel_transverse_epsilon :
    LinearMap.ker originalK = transverseEpsilonSpace D frame xAxis yAxis := by
  rw [original_K_kernel_eq_P_range D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis xDual yDual, native_P_range_transverse_epsilon]

end Spectrum

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
