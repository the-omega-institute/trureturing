import D5.S3.VertexAlgebra.TemporaryTransverseJointContraction14
import D5.S3.VertexAlgebra.TemporaryTransverseJointAuxiliary12
import Mathlib.LinearAlgebra.Basis.SMul
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

set_option autoImplicit false
namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section


def toggleOneEquiv : Finset ℕ ≃ Finset ℕ :=
  ⟨toggleOne, toggleOne, toggleOne_involutive, toggleOne_involutive⟩

theorem polarizationSign_ne_zero (subset : Finset ℕ) : polarizationSign subset ≠ 0 := by
  simp [polarizationSign]

def polarizationUnit (subset : Finset ℕ) : ℂˣ :=
  Units.mk0 (polarizationSign subset) (polarizationSign_ne_zero subset)

def ghostDownBasis : Module.Basis (Finset ℕ) ℂ (Fock ℂ) :=
  ((Finsupp.basisSingleOne : Module.Basis (Finset ℕ) ℂ (Fock ℂ)).reindex toggleOneEquiv).unitsSMul
    polarizationUnit

theorem ghostDownBasis_apply (subset : Finset ℕ) :
    ghostDownBasis subset = downWord subset down := by
  rw [signed_down_word]
  simp only [ghostDownBasis, Module.Basis.unitsSMul_apply, Module.Basis.reindex_apply,
    Finsupp.coe_basisSingleOne, Units.smul_def, polarizationUnit, Units.val_mk0]
  rfl

theorem original_ghost_finite_expansion (ghost : Fock ℂ) :
    ∑ subset ∈ (ghostDownBasis.repr ghost).support,
      ghostDownBasis.repr ghost subset • downWord subset down = ghost := by
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, ghostDownBasis_apply] using
    ghostDownBasis.linearCombination_repr ghost

theorem ghostDownBasis_original_coefficient (ghost : Fock ℂ) (subset : Finset ℕ) :
    ghostDownBasis.repr ghost subset = (polarizationSign subset)⁻¹ * ghost (toggleOne subset) := by
  rw [ghostDownBasis, Module.Basis.repr_unitsSMul, Module.Basis.repr_reindex_apply]
  change (polarizationUnit subset)⁻¹ • ghost (toggleOne subset) = _
  simp [Units.smul_def, polarizationUnit]

def coordinateEquiv (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1) :
    Oscillator D ≃ₗ[ℂ] Oscillator D :=
  LinearEquiv.ofBijective (coordinateSub D frame).toLinearMap
    (coordinateSub_bijective D frame inverse leftFrameInverse rightFrameInverse)

def coordinateMatterBasis (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1) :
    Module.Basis (Index D →₀ ℕ) ℂ (Oscillator D) :=
  (MvPolynomial.basisMonomials (Index D) ℂ).map
    (coordinateEquiv D frame inverse leftFrameInverse rightFrameInverse)

theorem coordinateMatterBasis_apply (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (powers : Index D →₀ ℕ) :
    coordinateMatterBasis D frame inverse leftFrameInverse rightFrameInverse powers =
      coordinateSub D frame (MvPolynomial.monomial powers 1) := by
  change coordinateEquiv D frame inverse leftFrameInverse rightFrameInverse
      (MvPolynomial.monomial powers 1) = _
  rfl

abbrev NativeIndex (D : LatticeData) := (Index D →₀ ℕ) × Finset ℕ

def nativeTensorBasis (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1) :
    Module.Basis (NativeIndex D) ℂ (Oscillator D ⊗[ℂ] Fock ℂ) :=
  (coordinateMatterBasis D frame inverse leftFrameInverse rightFrameInverse).tensorProduct ghostDownBasis

theorem nativeTensorBasis_apply (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (index : NativeIndex D) :
    nativeTensorBasis D frame inverse leftFrameInverse rightFrameInverse index =
      coordinateSub D frame (MvPolynomial.monomial index.1 1) ⊗ₜ[ℂ] downWord index.2 down := by
  rw [nativeTensorBasis, Module.Basis.tensorProduct_apply', coordinateMatterBasis_apply,
    ghostDownBasis_apply]

theorem chargeExtraction_embedding (D : LatticeData) (beta : Charge D)
    (input : Oscillator D ⊗[ℂ] Fock ℂ) :
    chargeExtraction D beta (chargeEmbedding D beta input) = input := by
  induction input using TensorProduct.induction_on with
  | zero => simp
  | tmul polynomial ghost =>
      simp [chargeExtraction, chargeEmbedding, TensorProduct.map_tmul,
        Finsupp.lsingle, Finsupp.lapply]
  | add first second firstProof secondProof => simp [firstProof, secondProof]

theorem chargeEmbedding_injective (D : LatticeData) (beta : Charge D) :
    Function.Injective (chargeEmbedding D beta) := by
  intro first second equalImages
  have equalInputs := congrArg (chargeExtraction D beta) equalImages
  simpa only [chargeExtraction_embedding] using equalInputs

def nativeWord (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (index : NativeIndex D) : State D :=
  Finsupp.single beta (coordinateSub D frame (MvPolynomial.monomial index.1 1)) ⊗ₜ[ℂ]
    downWord index.2 down

theorem nativeWord_scalar (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (powers : Index D →₀ ℕ) (scalar : ℂ) (subset : Finset ℕ) :
    Finsupp.single beta (coordinateSub D frame (MvPolynomial.monomial powers scalar)) ⊗ₜ[ℂ]
        downWord subset down = scalar • nativeWord D frame beta (powers, subset) := by
  have monomialScalar : MvPolynomial.monomial powers scalar =
      scalar • MvPolynomial.monomial powers (1 : ℂ) := by
    simp [MvPolynomial.monomial, Finsupp.smul_single]
  rw [monomialScalar, map_smul, ← Finsupp.smul_single, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul]
  rfl

theorem nativeWord_public_carrier_basis (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (beta : Charge D) (index : NativeIndex D) :
    TensorProduct.map (Finsupp.mapRange.linearMap (coordinateSub D frame).toLinearMap) LinearMap.id
      (LatticePositiveEnergy.carrierBasis D (beta, index.1) ⊗ₜ[ℂ] downWord index.2 down) =
      nativeWord D frame beta index := by
  simp only [LatticePositiveEnergy.carrierBasis_apply, TensorProduct.map_tmul,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, LinearMap.id_apply]
  rfl

theorem nativeWord_embedding (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (index : NativeIndex D) :
    nativeWord D frame beta index = chargeEmbedding D beta
        (nativeTensorBasis D frame inverse leftFrameInverse rightFrameInverse index) := by
  rw [← nativeWord_public_carrier_basis D frame beta index]
  rw [nativeTensorBasis_apply]
  simp only [LatticePositiveEnergy.carrierBasis_apply, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_single, chargeEmbedding, TensorProduct.map_tmul, Finsupp.lsingle, LinearMap.id_apply]
  rfl

def nativeSectorBasis (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) : Module.Basis (NativeIndex D) ℂ (LinearMap.range (chargeEmbedding D beta)) :=
  (nativeTensorBasis D frame inverse leftFrameInverse rightFrameInverse).map
    (LinearEquiv.ofInjective (chargeEmbedding D beta) (chargeEmbedding_injective D beta))

theorem nativeSectorBasis_apply (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (index : NativeIndex D) :
    (nativeSectorBasis D frame inverse leftFrameInverse rightFrameInverse beta index : State D) =
      nativeWord D frame beta index := by
  simp only [nativeSectorBasis, Module.Basis.map_apply, LinearEquiv.ofInjective_apply,
    nativeWord_embedding D frame inverse leftFrameInverse rightFrameInverse]

def nativeCoefficients (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) : State D →ₗ[ℂ] NativeIndex D →₀ ℂ :=
  (nativeTensorBasis D frame inverse leftFrameInverse rightFrameInverse).repr.toLinearMap.comp
    (chargeExtraction D beta)

theorem nativeCoefficients_word (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (index : NativeIndex D) :
    nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta
      (nativeWord D frame beta index) = Finsupp.single index 1 := by
  simp_rw [nativeWord_embedding D frame inverse leftFrameInverse rightFrameInverse beta]
  simp only [nativeCoefficients, LinearMap.comp_apply, chargeExtraction_embedding,
    LinearEquiv.coe_coe, Module.Basis.repr_self]

theorem nativeWord_sector (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (index : NativeIndex D) :
    chargeProjection D beta (nativeWord D frame beta index) = nativeWord D frame beta index := by
  apply (chargeEmbedding_range_iff D beta _).mp
  refine ⟨coordinateSub D frame (MvPolynomial.monomial index.1 1) ⊗ₜ[ℂ] downWord index.2 down, ?_⟩
  simp [nativeWord, chargeEmbedding, TensorProduct.map_tmul, Finsupp.lsingle]

theorem native_sector_finite_expansion (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (psi : State D) (sector : chargeProjection D beta psi = psi) :
    ∑ index ∈ (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi).support,
      nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi index •
        nativeWord D frame beta index = psi := by
  have expansion := (nativeTensorBasis D frame inverse leftFrameInverse rightFrameInverse).linearCombination_repr
    (chargeExtraction D beta psi)
  have embedded := congrArg (chargeEmbedding D beta) expansion
  change ∑ index ∈ ((nativeTensorBasis D frame inverse leftFrameInverse rightFrameInverse).repr
      (chargeExtraction D beta psi)).support,
      ((nativeTensorBasis D frame inverse leftFrameInverse rightFrameInverse).repr
        (chargeExtraction D beta psi)) index • nativeWord D frame beta index = psi
  conv_rhs => rw [← sector]
  simpa only [nativeWord, nativeTensorBasis_apply, Finsupp.linearCombination_apply,
    Finsupp.sum, map_sum, map_smul, chargeProjection, chargeEmbedding,
    TensorProduct.map_tmul, Finsupp.lsingle_apply,
    LinearMap.comp_apply, LinearMap.id_apply] using embedded

theorem native_sector_monomial_finite_expansion (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (psi : State D) (sector : chargeProjection D beta psi = psi) :
    ∑ index ∈ (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi).support,
      Finsupp.single beta (coordinateSub D frame (MvPolynomial.monomial index.1
        (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi index))) ⊗ₜ[ℂ]
          downWord index.2 down = psi := by
  simpa only [nativeWord_scalar] using
    native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse beta psi sector

theorem nativeWord_linearIndependent (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) : LinearIndependent ℂ (nativeWord D frame beta) := by
  have transported := (nativeTensorBasis D frame inverse leftFrameInverse rightFrameInverse).linearIndependent.map'
    (chargeEmbedding D beta) (LinearMap.ker_eq_bot.mpr (chargeEmbedding_injective D beta))
  simpa only [Function.comp_def,
    ← nativeWord_embedding D frame inverse leftFrameInverse rightFrameInverse] using transported

theorem nativeCoefficients_eq_zero_iff (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (psi : State D) (sector : chargeProjection D beta psi = psi) :
    nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi = 0 ↔ psi = 0 := by
  constructor
  · intro zeroCoefficients
    have expansion := native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse beta psi sector
    simpa [zeroCoefficients] using expansion.symm
  · rintro rfl
    exact map_zero _

theorem native_nonzero_coefficient (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (psi : State D) (sector : chargeProjection D beta psi = psi)
    (nonzero : psi ≠ 0) : ∃ index, nativeCoefficients D frame inverse
      leftFrameInverse rightFrameInverse beta psi index ≠ 0 := by
  by_contra noCoefficient
  apply nonzero
  apply (nativeCoefficients_eq_zero_iff D frame inverse leftFrameInverse rightFrameInverse beta psi sector).mp
  ext index
  simpa using (not_exists.mp noCoefficient) index

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
