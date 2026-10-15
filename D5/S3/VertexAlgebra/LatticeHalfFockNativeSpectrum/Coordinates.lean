/- GID: D5/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/Coordinates
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/Coordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete native tensor coefficients and exact L0 occupation support. -/

import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
import D5.S3.VertexAlgebra.LatticeInvolution

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum

open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

abbrev Occupation (D : LatticeData) := Index D →₀ ℕ

def coefficients (D : LatticeData) (hu : IsUnit D.G.det) :
    ActualTensor D hu ≃ₗ[ℂ] Occupation D →₀ ActualGround D hu :=
  TensorProduct.equivFinsuppOfBasisLeft (MvPolynomial.basisMonomials (Index D) ℂ)

theorem coefficients_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (polynomial : Oscillator D) (ground : ActualGround D hu) (exponent : Occupation D) :
    coefficients D hu (polynomial ⊗ₜ[ℂ] ground) exponent = coeff exponent polynomial • ground := by
  exact TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply _ _ _ _

theorem inverse_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (coordinates : Occupation D →₀ ActualGround D hu) :
    (coefficients D hu).symm coordinates =
      ∑ exponent ∈ coordinates.support, monomial exponent (1 : ℂ) ⊗ₜ[ℂ] coordinates exponent := by
  exact TensorProduct.equivFinsuppOfBasisLeft_symm_apply _ _

def occupationWeight (D : LatticeData) (exponent : Occupation D) : ℕ :=
  Finsupp.weight (fun index : Index D => 2 * index.2 + 1) exponent

def weightValue (D : LatticeData) (level : ℕ) : ℂ := (D.rank : ℂ) / 16 + (level : ℂ) / 2

theorem half_weight (D : LatticeData) (exponent : Occupation D) :
    ∑ index ∈ exponent.support, (exponent index : ℂ) * ((index.2 : ℂ) + 1 / 2) =
      (occupationWeight D exponent : ℂ) / 2 := by
  classical
  simp only [occupationWeight, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro index member
  ring

def nativeL0 (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Module.End ℂ (ActualTensor D hu) :=
  tensorL D (ActualGround D hu) H 0

theorem coefficient_diagonalization (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : ActualTensor D hu) (exponent : Occupation D) :
    coefficients D hu (nativeL0 D hu H state) exponent =
      weightValue D (occupationWeight D exponent) • coefficients D hu state exponent := by
  classical
  obtain ⟨coordinates, rfl⟩ := (coefficients D hu).symm.surjective state
  rw [inverse_expansion]
  simp only [map_sum, Finsupp.finsetSum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro degree member
  change coefficients D hu (tensorEnd D (ActualGround D hu)
    (L D H 0) (monomial degree (1 : ℂ) ⊗ₜ[ℂ] coordinates degree)) exponent = _
  rw [tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply,
    L_zero_monomial_coeff D H hHG hGH, half_weight,
    ← TensorProduct.smul_tmul', map_smul]
  simp only [Finsupp.coe_smul, Pi.smul_apply, coefficients_tmul, coeff_monomial]
  by_cases equality : degree = exponent
  · subst degree
    simp [weightValue]
  · simp [equality]

def eigenspace (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (value : ℂ) : Submodule ℂ (ActualTensor D hu) :=
  LinearMap.ker (nativeL0 D hu H - value • LinearMap.id)

theorem eigen_support_iff (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (value : ℂ) (state : ActualTensor D hu) :
    state ∈ eigenspace D hu H value ↔
      ∀ exponent, weightValue D (occupationWeight D exponent) ≠ value →
        coefficients D hu state exponent = 0 := by
  classical
  change nativeL0 D hu H state - value • state = 0 ↔ _
  rw [sub_eq_zero, ← (coefficients D hu).injective.eq_iff]
  simp only [map_smul]
  constructor
  · intro equality exponent different
    have coordinate := congrArg (fun coordinates => coordinates exponent) equality
    rw [coefficient_diagonalization D hu H hHG hGH] at coordinate
    have zero : (weightValue D (occupationWeight D exponent) - value) •
        coefficients D hu state exponent = 0 := by
      rw [sub_smul, coordinate]
      simp
    exact (smul_eq_zero.mp zero).resolve_left (sub_ne_zero.mpr different)
  · intro support
    ext exponent
    rw [coefficient_diagonalization D hu H hHG hGH]
    by_cases equality : weightValue D (occupationWeight D exponent) = value
    · simp [equality]
    · simp [support exponent equality]

theorem weightValue_injective (D : LatticeData) : Function.Injective (weightValue D) := by
  intro left right equality
  have cast : (left : ℂ) = (right : ℂ) := by
    unfold weightValue at equality
    linear_combination 2 * equality
  exact_mod_cast cast

end
end D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum
