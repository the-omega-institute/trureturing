import D5.S3.VertexAlgebra.TemporaryTransverseJointContraction15
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

theorem positive_modes_up (mode : ℤ) (positive : 0 < mode) :
    b (K := ℂ) mode up = 0 ∧ c (K := ℂ) mode up = 0 := by
  obtain ⟨bDown, cDown⟩ := positive_modes_down mode positive
  constructor
  · have equality := congrArg (fun operator : Module.End ℂ (Fock ℂ) => operator down)
      (BcGhostStressCurrent.b_c (K := ℂ) mode 0)
    simpa [Module.End.mul_apply, bDown, up, ne_of_gt positive] using equality
  · have equality := congrArg (fun operator : Module.End ℂ (Fock ℂ) => operator down)
      (BcGhostStressCurrent.c_c (K := ℂ) mode 0)
    simpa [Module.End.mul_apply, cDown, up] using equality

theorem downWord_only_epsilon (subset : Finset ℕ) (onlyEpsilon : subset ⊆ {3}) :
    downWord subset down = if 3 ∈ subset then up else down := by
  classical
  by_cases epsilonPresent : 3 ∈ subset
  · have equality : subset = {3} :=
      Finset.Subset.antisymm onlyEpsilon (Finset.singleton_subset_iff.mpr epsilonPresent)
    subst subset
    simp [downWord, downCreator, up, c]
  · have equality : subset = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro site member
      have atEpsilon := Finset.mem_singleton.mp (onlyEpsilon member)
      exact epsilonPresent (atEpsilon ▸ member)
    simp [equality, downWord]

theorem positive_modes_only_epsilon (subset : Finset ℕ) (onlyEpsilon : subset ⊆ {3})
    (mode : ℤ) (positive : 0 < mode) :
    b (K := ℂ) mode (downWord subset down) = 0 ∧
      c (K := ℂ) mode (downWord subset down) = 0 := by
  rw [downWord_only_epsilon subset onlyEpsilon]
  split_ifs
  · exact positive_modes_up mode positive
  · exact positive_modes_down mode positive

theorem directionalCurrent_positive_transverse_zero (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (direction : Fin D.rank → ℂ)
    (axis : Fin D.rank)
    (dual : ∀ row, gramPair D direction (frame row) = if row = axis then 1 else 0)
    (charge : Charge D) (powers : Index D →₀ ℕ) (scalar : ℂ)
    (axisZero : ∀ frequency : ℕ, powers (axis, frequency) = 0)
    (mode : ℤ) (positive : 0 < mode) :
    directionalCurrent D direction mode
      (Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar))) = 0 := by
  let frequency := (mode - 1).toNat
  have modeEquality : mode = (frequency : ℤ) + 1 := by dsimp [frequency]; omega
  rw [modeEquality, directionalCurrent_single, directionalPolynomialCurrent_positive,
    coordinateDerivative_axis D frame direction axis frequency dual]
  simp [MvPolynomial.pderiv_monomial, axisZero frequency]

theorem original_dAtom_zero_occupation (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (charge : Charge D) (powers : Index D →₀ ℕ) (scalar : ℂ) (subset : Finset ℕ)
    (zero : kappa D xAxis yAxis powers subset = 0) (mode : ℤ) :
    dAtom D (frame yAxis) mode (nativeState D frame charge powers scalar subset) = 0 := by
  obtain ⟨xZero, yZero, onlyEpsilon⟩ := (kappa_zero_iff D xAxis yAxis powers subset).mp zero
  by_cases zeroMode : mode = 0
  · simp [dAtom, zeroMode]
  by_cases positive : 0 < mode
  · have matterZero := directionalCurrent_positive_transverse_zero D frame (frame yAxis)
      xAxis xDual charge powers scalar xZero mode positive
    simp [nativeState, dAtom, zeroMode, C, O, Module.End.mul_apply, matterZero]
  · have ghostZero := (positive_modes_only_epsilon subset onlyEpsilon (-mode) (by omega)).2
    simp [nativeState, dAtom, zeroMode, C, O, Module.End.mul_apply, ghostZero]

theorem original_rAtom_zero_occupation (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (charge : Charge D) (powers : Index D →₀ ℕ) (scalar : ℂ) (subset : Finset ℕ)
    (zero : kappa D xAxis yAxis powers subset = 0) (mode : ℤ) :
    rAtom D (frame xAxis) mode (nativeState D frame charge powers scalar subset) = 0 := by
  obtain ⟨xZero, yZero, onlyEpsilon⟩ := (kappa_zero_iff D xAxis yAxis powers subset).mp zero
  by_cases zeroMode : mode = 0
  · simp [rAtom, zeroMode]
  by_cases positive : 0 < mode
  · have ghostZero := (positive_modes_only_epsilon subset onlyEpsilon mode positive).1
    simp [nativeState, rAtom, zeroMode, B, O, Module.End.mul_apply, ghostZero]
  · have matterZero := directionalCurrent_positive_transverse_zero D frame (frame xAxis)
      yAxis yDual charge powers scalar yZero (-mode) (by omega)
    simp [nativeState, rAtom, zeroMode, B, O, Module.End.mul_apply, matterZero]

theorem original_delta_zero_occupation (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (charge : Charge D) (powers : Index D →₀ ℕ) (scalar : ℂ) (subset : Finset ℕ)
    (zero : kappa D xAxis yAxis powers subset = 0) (coefficient : ℂ) :
    delta D (frame yAxis) coefficient (nativeState D frame charge powers scalar subset) = 0 := by
  change coefficient • (∑ᶠ mode : ℤ,
    dAtom D (frame yAxis) mode (nativeState D frame charge powers scalar subset)) = 0
  simp_rw [original_dAtom_zero_occupation D frame xAxis yAxis xDual charge powers scalar subset zero]
  simp

theorem original_R_zero_occupation (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (charge : Charge D) (powers : Index D →₀ ℕ) (scalar : ℂ) (subset : Finset ℕ)
    (zero : kappa D xAxis yAxis powers subset = 0) (coefficient : ℂ) :
    R D (frame xAxis) coefficient (nativeState D frame charge powers scalar subset) = 0 := by
  change coefficient⁻¹ • (∑ᶠ mode : ℤ,
    rAtom D (frame xAxis) mode (nativeState D frame charge powers scalar subset)) = 0
  simp_rw [original_rAtom_zero_occupation D frame xAxis yAxis yDual charge powers scalar subset zero]
  simp

theorem B_zero_original_coefficient_basis (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (index : NativeCoefficientIndex D) :
    B D 0 (nativeCoefficientBasis D frame inverse leftFrameInverse rightFrameInverse index) =
      (if 3 ∈ index.2 then sign (K := ℂ) 3 index.2 else 0) •
      nativeCoefficientBasis D frame inverse leftFrameInverse rightFrameInverse (index.1, index.2.erase 3) := by
  rw [nativeCoefficientBasis_apply, nativeCoefficientBasis_apply]
  by_cases present : 3 ∈ index.2 <;>
    simp [B, b, annihilate, annihilateBasis, present, TensorProduct.tmul_smul] <;>
    rw [← TensorProduct.tmul_smul, Finsupp.smul_single] <;> simp

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
