import D5.S3.VertexAlgebra.TemporaryTransverseJointContraction13
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

def nativeState (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (charge : Charge D) (powers : Index D →₀ ℕ) (scalar : ℂ) (subset : Finset ℕ) : State D :=
  Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar))
    ⊗ₜ[ℂ] downWord subset down

theorem toggleOne_involutive : Function.Involutive toggleOne := by
  intro subset
  by_cases present : 1 ∈ subset
  · simp [toggleOne, present, Finset.insert_erase present]
  · simp [toggleOne, present]

theorem polarizationSign_square (subset : Finset ℕ) :
    polarizationSign subset * polarizationSign subset = 1 := by
  simp [polarizationSign, ← mul_pow]

theorem polarizationSign_nonzero (subset : Finset ℕ) : polarizationSign subset ≠ 0 := by
  exact pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)

theorem original_ghost_single_from_signed (subset : Finset ℕ) :
    Finsupp.single subset (1 : ℂ) =
      polarizationSign (toggleOne subset) • downWord (toggleOne subset) down := by
  rw [signed_down_word]
  simp only [polarizedBasis, smul_smul, toggleOne_involutive,
    polarizationSign_square, one_smul]
  rw [toggleOne_involutive subset]

def coordinateLinearEquiv (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1) :
    Oscillator D ≃ₗ[ℂ] Oscillator D where
  toLinearMap := (coordinateSub D frame).toLinearMap
  invFun := coordinateSub D inverse
  left_inv := coordinateSub_inverse D inverse frame rightFrameInverse
  right_inv := coordinateSub_inverse D frame inverse leftFrameInverse

abbrev NativeCoefficientIndex (D : LatticeData) :=
  (Σ charge : Charge D, Index D →₀ ℕ) × Finset ℕ

def nativeCoefficientBasis (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1) :
    Module.Basis (NativeCoefficientIndex D) ℂ (State D) :=
  (Finsupp.basis (fun _ : Charge D =>
    (MvPolynomial.basisMonomials (Index D) ℂ).map
      (coordinateLinearEquiv D frame inverse leftFrameInverse rightFrameInverse))).tensorProduct
    (Finsupp.basisSingleOne : Module.Basis (Finset ℕ) ℂ (Fock ℂ))

section Coefficients

variable (D : LatticeData) (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)

local notation "nativeBasis" => nativeCoefficientBasis D frame inverse leftFrameInverse rightFrameInverse

theorem nativeCoefficientBasis_apply (index : NativeCoefficientIndex D) :
    nativeBasis index =
      Finsupp.single index.1.1 (coordinateSub D frame (MvPolynomial.monomial index.1.2 1))
        ⊗ₜ[ℂ] Finsupp.single index.2 1 := by
  simp [nativeCoefficientBasis, Module.Basis.tensorProduct_apply', Finsupp.coe_basis, MvPolynomial.coe_basisMonomials,
    coordinateLinearEquiv] <;> rfl

theorem nativeCoefficientBasis_repr_tmul (matter : Carrier D) (ghost : Fock ℂ)
    (index : NativeCoefficientIndex D) :
    (nativeBasis).repr (matter ⊗ₜ[ℂ] ghost) index =
      ghost index.2 * MvPolynomial.coeff index.1.2 (coordinateSub D inverse (matter index.1.1)) := by
  rcases index with ⟨⟨charge, powers⟩, subset⟩
  simp only [nativeCoefficientBasis, Module.Basis.tensorProduct_repr_tmul_apply,
    Finsupp.basis_repr, Module.Basis.map, coordinateLinearEquiv,
    Finsupp.basisSingleOne, Module.Basis.ofRepr, smul_eq_mul] <;> rfl

theorem nativeState_as_coefficient_basis (charge : Charge D) (powers : Index D →₀ ℕ)
    (scalar : ℂ) (subset : Finset ℕ) :
    nativeState D frame charge powers scalar subset =
      (scalar * polarizationSign subset) • nativeBasis (⟨charge, powers⟩, toggleOne subset) := by
  have scalarMonomial : MvPolynomial.monomial powers scalar =
      scalar • MvPolynomial.monomial powers (1 : ℂ) := by simp [MvPolynomial.smul_monomial]
  rw [nativeState, signed_down_word, polarizedBasis, scalarMonomial,
    nativeCoefficientBasis_apply]
  simp only [map_smul, ← Finsupp.smul_single, ← TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, smul_smul]
  rw [mul_comm]

theorem nativeCoefficientBasis_as_signed (index : NativeCoefficientIndex D) :
    nativeBasis index = polarizationSign (toggleOne index.2) •
      nativeState D frame index.1.1 index.1.2 1 (toggleOne index.2) := by
  rw [nativeState_as_coefficient_basis D frame inverse leftFrameInverse rightFrameInverse]
  simp only [one_mul, smul_smul, polarizationSign_square, toggleOne_involutive index.2, one_smul]

def coefficientDiagonal (eigenvalue : NativeCoefficientIndex D → ℂ) : Module.End ℂ (State D) :=
  (nativeBasis).constr ℂ (fun index => eigenvalue index • nativeBasis index)

theorem coefficientDiagonal_basis (eigenvalue : NativeCoefficientIndex D → ℂ)
    (index : NativeCoefficientIndex D) :
    coefficientDiagonal D frame inverse leftFrameInverse rightFrameInverse eigenvalue
      (nativeBasis index) = eigenvalue index • nativeBasis index := by
  simp [coefficientDiagonal]

theorem coefficientDiagonal_repr (eigenvalue : NativeCoefficientIndex D → ℂ)
    (state : State D) (index : NativeCoefficientIndex D) :
    (nativeBasis).repr
      (coefficientDiagonal D frame inverse leftFrameInverse rightFrameInverse eigenvalue state) index =
      eigenvalue index * (nativeBasis).repr state index := by
  have identity :
      (Finsupp.lapply index).comp ((nativeBasis).repr.toLinearMap.comp
        (coefficientDiagonal D frame inverse leftFrameInverse rightFrameInverse eigenvalue)) =
      eigenvalue index • ((Finsupp.lapply index).comp (nativeBasis).repr.toLinearMap) := by
    apply (nativeBasis).ext
    intro other
    by_cases same : other = index <;>
      simp [coefficientDiagonal_basis, same, Finsupp.single_apply, eq_comm]
  exact congrArg (fun operator : State D →ₗ[ℂ] ℂ => operator state) identity


def nativeOccupation (xAxis yAxis : Fin D.rank) (index : NativeCoefficientIndex D) : ℕ :=
  kappa D xAxis yAxis index.1.2 (toggleOne index.2)

def Kdagger (xAxis yAxis : Fin D.rank) : Module.End ℂ (State D) :=
  coefficientDiagonal D frame inverse leftFrameInverse rightFrameInverse
    (fun index => (nativeOccupation D xAxis yAxis index : ℂ)⁻¹)

def P (xAxis yAxis : Fin D.rank) : Module.End ℂ (State D) :=
  coefficientDiagonal D frame inverse leftFrameInverse rightFrameInverse
    (fun index => if nativeOccupation D xAxis yAxis index = 0 then 1 else 0)

theorem Kdagger_basis (xAxis yAxis : Fin D.rank) (index : NativeCoefficientIndex D) :
    Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis (nativeBasis index) =
      (nativeOccupation D xAxis yAxis index : ℂ)⁻¹ • nativeBasis index := by
  exact coefficientDiagonal_basis D frame inverse leftFrameInverse rightFrameInverse _ index

theorem P_basis (xAxis yAxis : Fin D.rank) (index : NativeCoefficientIndex D) :
    P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis (nativeBasis index) =
      (if nativeOccupation D xAxis yAxis index = 0 then 1 else 0 : ℂ) • nativeBasis index := by
  exact coefficientDiagonal_basis D frame inverse leftFrameInverse rightFrameInverse _ index

theorem Kdagger_native (xAxis yAxis : Fin D.rank) (charge : Charge D)
    (powers : Index D →₀ ℕ) (scalar : ℂ) (subset : Finset ℕ) :
    Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
      (nativeState D frame charge powers scalar subset) =
      (kappa D xAxis yAxis powers subset : ℂ)⁻¹ •
        nativeState D frame charge powers scalar subset := by
  rw [nativeState_as_coefficient_basis D frame inverse leftFrameInverse rightFrameInverse
    charge powers scalar subset, map_smul, Kdagger_basis]
  simp only [nativeOccupation, toggleOne_involutive subset]
  rw [smul_comm]

theorem P_native (xAxis yAxis : Fin D.rank) (charge : Charge D)
    (powers : Index D →₀ ℕ) (scalar : ℂ) (subset : Finset ℕ) :
    P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
      (nativeState D frame charge powers scalar subset) =
      (if kappa D xAxis yAxis powers subset = 0 then 1 else 0 : ℂ) •
        nativeState D frame charge powers scalar subset := by
  rw [nativeState_as_coefficient_basis D frame inverse leftFrameInverse rightFrameInverse
    charge powers scalar subset, map_smul, P_basis]
  simp only [nativeOccupation, toggleOne_involutive subset]
  rw [smul_comm]

variable (xAxis yAxis : Fin D.rank)
  (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
  (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)

local notation "originalK" => K D (frame xAxis) (frame yAxis) (Eq.trans (xDual xAxis) (if_pos (Eq.refl xAxis)))
local notation "inverseK" => Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
local notation "projector" => P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis

include yDual in
theorem original_K_coefficient_basis (index : NativeCoefficientIndex D) :
    originalK (nativeBasis index) =
      (nativeOccupation D xAxis yAxis index : ℂ) • nativeBasis index := by
  rw [nativeCoefficientBasis_as_signed, map_smul]
  rw [show originalK (nativeState D frame index.1.1 index.1.2 1 (toggleOne index.2)) =
    (kappa D xAxis yAxis index.1.2 (toggleOne index.2) : ℂ) •
      nativeState D frame index.1.1 index.1.2 1 (toggleOne index.2) from
    original_K_all_frequency_count D frame xAxis yAxis xDual yDual _ _ _ _]
  rw [smul_comm]
  rfl

include yDual in
theorem original_K_coefficient_diagonal : originalK =
    coefficientDiagonal D frame inverse leftFrameInverse rightFrameInverse
      (fun index => (nativeOccupation D xAxis yAxis index : ℂ)) := by
  apply (nativeBasis).ext
  intro index
  rw [original_K_coefficient_basis D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis xDual yDual, coefficientDiagonal_basis]

include yDual in
theorem original_K_repr (state : State D) (index : NativeCoefficientIndex D) :
    (nativeBasis).repr (originalK state) index =
      (nativeOccupation D xAxis yAxis index : ℂ) * (nativeBasis).repr state index := by
  rw [original_K_coefficient_diagonal D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis xDual yDual]
  exact coefficientDiagonal_repr D frame inverse leftFrameInverse rightFrameInverse _ state index

include yDual in
theorem original_K_Kdagger : originalK * inverseK = 1 - projector := by
  apply (nativeBasis).ext
  intro index
  simp only [Module.End.mul_apply, Kdagger_basis, map_smul,
    original_K_coefficient_basis D frame inverse leftFrameInverse rightFrameInverse
      xAxis yAxis xDual yDual, LinearMap.sub_apply, Module.End.one_apply, P_basis, smul_smul]
  by_cases zero : nativeOccupation D xAxis yAxis index = 0
  · simp [zero]
  · have nonzero : (nativeOccupation D xAxis yAxis index : ℂ) ≠ 0 := by exact_mod_cast zero
    simp [zero, nonzero]

include yDual in
theorem original_Kdagger_K : inverseK * originalK = 1 - projector := by
  apply (nativeBasis).ext
  intro index
  simp only [Module.End.mul_apply,
    original_K_coefficient_basis D frame inverse leftFrameInverse rightFrameInverse
      xAxis yAxis xDual yDual, map_smul, Kdagger_basis,
    LinearMap.sub_apply, Module.End.one_apply, P_basis, smul_smul]
  by_cases zero : nativeOccupation D xAxis yAxis index = 0
  · simp [zero]
  · have nonzero : (nativeOccupation D xAxis yAxis index : ℂ) ≠ 0 := by exact_mod_cast zero
    simp [zero, nonzero]

theorem native_P_idempotent : projector * projector = projector := by
  apply (nativeBasis).ext
  intro index
  simp only [Module.End.mul_apply, P_basis, map_smul, smul_smul]
  split_ifs <;> simp

theorem native_Kdagger_P_zero : inverseK * projector = 0 := by
  apply (nativeBasis).ext
  intro index
  simp only [Module.End.mul_apply, P_basis, map_smul, Kdagger_basis, smul_smul,
    LinearMap.zero_apply]
  by_cases zero : nativeOccupation D xAxis yAxis index = 0 <;> simp [zero]

theorem native_P_Kdagger_zero : projector * inverseK = 0 := by
  apply (nativeBasis).ext
  intro index
  simp only [Module.End.mul_apply, Kdagger_basis, map_smul, P_basis, smul_smul,
    LinearMap.zero_apply]
  by_cases zero : nativeOccupation D xAxis yAxis index = 0 <;> simp [zero]

include yDual in
theorem original_K_P_zero : originalK * projector = 0 := by
  apply (nativeBasis).ext
  intro index
  simp only [Module.End.mul_apply, P_basis, map_smul,
    original_K_coefficient_basis D frame inverse leftFrameInverse rightFrameInverse
      xAxis yAxis xDual yDual, smul_smul, LinearMap.zero_apply]
  by_cases zero : nativeOccupation D xAxis yAxis index = 0 <;> simp [zero]

include yDual in
theorem original_K_kernel_eq_P_range : LinearMap.ker originalK = LinearMap.range projector := by
  ext state
  constructor
  · intro killed
    have equality := congrArg (fun operator : Module.End ℂ (State D) => operator state)
      (original_Kdagger_K D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis xDual yDual)
    have kernelEquality : originalK state = 0 := killed
    simp only [Module.End.mul_apply, kernelEquality, map_zero, LinearMap.sub_apply,
      Module.End.one_apply] at equality
    exact ⟨state, (sub_eq_zero.mp equality.symm).symm⟩
  · rintro ⟨preimage, rfl⟩
    have equality := congrArg (fun operator : Module.End ℂ (State D) => operator preimage)
      (original_K_P_zero D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis xDual yDual)
    exact equality

end Coefficients

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
