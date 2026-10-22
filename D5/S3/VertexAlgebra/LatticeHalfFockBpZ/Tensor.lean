/- GID: D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Tensor
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockBpZ/Tensor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original chosen Leech tensor has a symmetric nondegenerate BPZ bilinear form. -/

import D5.S3.VertexAlgebra.LatticeHalfFockBpZ.Oscillator
import D5.S3.VertexAlgebra.TwistedGround.NativeSymmetricForm
import D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Leech
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

set_option autoImplicit false
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockBpZ

open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients
open GolayLeech.ExplicitLeechLattice TwistedGround.NativeHyperbolicActions
open TwistedGround.NativeOrbit TwistedGround.NativeSymmetricForm
open scoped BigOperators TensorProduct

noncomputable section

abbrev NativeTensor := ActualTensor data determinantUnit

def tensorPairing : LinearMap.BilinForm ℂ NativeTensor :=
  (oscillatorPairing data).tmul nativePairing

theorem tensor_pairing_tmul (first second : Oscillator data) (left right : NativeGround) :
    tensorPairing (first ⊗ₜ[ℂ] left) (second ⊗ₜ[ℂ] right) =
      oscillatorPairing data first second * nativePairing left right := by
  change nativePairing left right * oscillatorPairing data first second = _
  exact mul_comm _ _

theorem tensor_pairing_symm : tensorPairing.IsSymm :=
  LinearMap.BilinForm.isSymm_iff.mpr (LinearMap.IsSymm.tmul
    (LinearMap.BilinForm.isSymm_iff.mp (oscillator_pairing_symm data))
    (LinearMap.BilinForm.isSymm_iff.mp native_pairing_symm))

def groundCoordinates : NativeTensor ≃ₗ[ℂ]
    LatticeTwistedGroundRealization.Half 12 →₀ Oscillator data :=
  TensorProduct.equivFinsuppOfBasisRight nativeBasis

private theorem ground_basis_coordinate (ground : NativeGround)
    (half : LatticeTwistedGroundRealization.Half 12) :
    nativePairing ground (nativeBasis half) = nativeBasis.repr ground half := by
  have identity : nativePairing.flip (nativeBasis half) = nativeBasis.coord half := by
    apply nativeBasis.ext
    intro other
    change nativePairing (nativeBasis other) (nativeBasis half) =
      nativeBasis.coord half (nativeBasis other)
    rw [basis_pairing]
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      eq_comm]
  exact congrArg (fun functional : NativeGround →ₗ[ℂ] ℂ => functional ground) identity

theorem tensor_pairing_coordinate (state : NativeTensor) (polynomial : Oscillator data)
    (half : LatticeTwistedGroundRealization.Half 12) :
    tensorPairing state (polynomial ⊗ₜ[ℂ] nativeBasis half) =
      oscillatorPairing data (groundCoordinates state half) polynomial := by
  induction state using TensorProduct.induction_on with
  | zero => simp
  | tmul first ground =>
    rw [tensor_pairing_tmul, ground_basis_coordinate]
    simp only [groundCoordinates, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
      map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  | add first second firstProof secondProof =>
    simp only [map_add, LinearMap.add_apply, Finsupp.add_apply, firstProof, secondProof]

theorem tensor_pairing_nondegenerate
    (H : Matrix (Fin data.rank) (Fin data.rank) ℂ)
    (leftInverse : H * gramComplex data = 1)
    (rightInverse : gramComplex data * H = 1) : tensorPairing.Nondegenerate := by
  have separation := oscillator_pairing_nondegenerate data H leftInverse rightInverse
  have leftSeparating : tensorPairing.SeparatingLeft := by
    intro state radical
    apply groundCoordinates.injective
    apply Finsupp.ext
    intro half
    change groundCoordinates state half = 0
    apply separation.1
    intro polynomial
    rw [← tensor_pairing_coordinate]
    exact radical (polynomial ⊗ₜ[ℂ] nativeBasis half)
  constructor
  · exact leftSeparating
  · intro state radical
    apply leftSeparating
    intro other
    rw [tensor_pairing_symm.eq]
    exact radical other

theorem tensor_current_adjoint (axis : Fin data.rank) (mode : ℤ)
    (first second : NativeTensor) :
    tensorPairing (tensorCurrent data NativeGround axis mode first) second =
      -tensorPairing first (tensorCurrent data NativeGround axis (-mode - 1) second) := by
  induction first using TensorProduct.induction_on with
  | zero => simp
  | tmul first ground =>
    induction second using TensorProduct.induction_on with
    | zero => simp
    | tmul second other =>
      change tensorPairing
        ((current data axis mode first) ⊗ₜ[ℂ] ground) (second ⊗ₜ[ℂ] other) =
        -tensorPairing (first ⊗ₜ[ℂ] ground)
          ((current data axis (-mode - 1) second) ⊗ₜ[ℂ] other)
      rw [tensor_pairing_tmul, tensor_pairing_tmul, oscillator_current_adjoint]
      ring
    | add first second firstProof secondProof =>
      simp only [map_add, neg_add, firstProof, secondProof]
  | add first second firstProof secondProof =>
    simp only [map_add, LinearMap.add_apply, neg_add, firstProof, secondProof]

end
end D5.S3.VertexAlgebra.LatticeHalfFockBpZ
