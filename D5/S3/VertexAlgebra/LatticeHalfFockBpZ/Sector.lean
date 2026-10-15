/- GID: D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Sector
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockBpZ/Sector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original theta invariance and both zero radicals on the literal odd W carrier. -/

import D5.S3.VertexAlgebra.LatticeHalfFockBpZ.Stress
import D5.S3.VertexAlgebra.LatticeHalfFockIntegralOddFixedSector

set_option autoImplicit false
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockBpZ

open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockNativeSpectrum
open LatticeHalfFockChargedTensorCoefficients LatticeInvolution
open LatticeHalfFockTargetThetaCoefficients LatticeHalfFockTargetThetaFixed
open GolayLeech.ExplicitLeechLattice TwistedGround.NativeHyperbolicActions
open LatticeOscillatorFockForm MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

private theorem scale_constantCoeff (D : LatticeData) (scalars : ℕ → ℂ)
    (polynomial : Oscillator D) :
    constantCoeff (scalePolynomial D scalars polynomial) = constantCoeff polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [scalePolynomial_C]
  | add first second firstProof secondProof => simp [map_add, firstProof, secondProof]
  | mul_X polynomial index inductionProof => simp [map_mul, scalePolynomial_X]

private theorem sigma_constantCoeff (D : LatticeData) (polynomial : Oscillator D) :
    constantCoeff (sigma D polynomial) = constantCoeff polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp
  | add first second firstProof secondProof => simp [map_add, firstProof, secondProof]
  | mul_X polynomial index inductionProof => simp [map_mul]

private theorem oscillator_constant_left (D : LatticeData) (scalar : ℂ)
    (polynomial : Oscillator D) :
    oscillatorPairing D (C scalar) polynomial = scalar * constantCoeff polynomial := by
  rw [oscillator_pairing_apply]
  change gramBilinear D (scalePolynomial D modeScale (C scalar))
    (scalePolynomial D modeScale polynomial) = _
  rw [scalePolynomial_C]
  have integer : gramBilinear D (C scalar) (scalePolynomial D modeScale polynomial) =
      scalar * constantCoeff (scalePolynomial D modeScale polynomial) := by
    run_tac
      let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeOscillatorFockForm 0).append
        `D5.S3.VertexAlgebra.LatticeOscillatorFockForm.gramBilinear_constant_left
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent supplier) _ _ _))
  rw [integer, scale_constantCoeff]

private theorem current_sigma_positive (D : LatticeData) (index : Index D)
    (polynomial : Oscillator D) :
    current D index.1 (index.2 : ℤ) (sigma D polynomial) =
      -sigma D (current D index.1 (index.2 : ℤ) polynomial) := by
  simp only [current, if_neg (show ¬ (index.2 : ℤ) < 0 by omega),
    Int.toNat_natCast, LinearMap.smul_apply, LatticeActualAnnihilation.annihilate,
    LatticeSugawaraCurrents.weightedPartial, LinearMap.sum_apply,
    Derivation.coeFn_coe, map_sum, sigma_smul, sigma_pderiv,
    smul_neg, Finset.sum_neg_distrib, neg_neg]

theorem oscillator_theta_invariant (D : LatticeData) (first second : Oscillator D) :
    oscillatorPairing D (sigma D first) (sigma D second) =
      oscillatorPairing D first second := by
  induction first using MvPolynomial.induction_on generalizing second with
  | C scalar => simp [oscillator_constant_left, sigma_constantCoeff]
  | add first third firstProof thirdProof =>
    simp only [map_add, LinearMap.add_apply, firstProof, thirdProof]
  | mul_X polynomial index inductionProof =>
    rw [mul_comm polynomial (X index), map_mul, sigma_X, neg_mul,
      map_neg, LinearMap.neg_apply]
    rw [oscillator_creator_adjoint, neg_neg, current_sigma_positive, map_neg]
    rw [inductionProof, oscillator_creator_adjoint]

theorem tensor_theta_invariant (first second : NativeTensor) :
    tensorPairing (sigmaTensor data determinantUnit first)
      (sigmaTensor data determinantUnit second) = tensorPairing first second := by
  induction first using TensorProduct.induction_on with
  | zero => simp
  | tmul first ground =>
    induction second using TensorProduct.induction_on with
    | zero => simp
    | tmul second other =>
      rw [sigmaTensor_tmul, sigmaTensor_tmul, tensor_pairing_tmul,
        tensor_pairing_tmul, oscillator_theta_invariant]
    | add first second firstProof secondProof =>
      simp only [map_add, firstProof, secondProof]
  | add first second firstProof secondProof =>
    simp only [map_add, LinearMap.add_apply, firstProof, secondProof]

theorem tensor_theta_adjoint (first second : NativeTensor) :
    tensorPairing (sigmaTensor data determinantUnit first) second =
      tensorPairing first (sigmaTensor data determinantUnit second) := by
  have equation := tensor_theta_invariant first (sigmaTensor data determinantUnit second)
  rw [sigmaTensor_involutive data determinantUnit second] at equation
  exact equation

abbrev NativeW := ↥(oddTarget data determinantUnit)

def oddProjection : NativeTensor →ₗ[ℂ] NativeW where
  toFun state := ⟨(2 : ℂ)⁻¹ • (state - sigmaTensor data determinantUnit state), by
    rw [mem_oddTarget]
    simp only [map_smul, map_sub, sigmaTensor_involutive data determinantUnit state]
    module⟩
  map_add' first second := by
    apply Subtype.ext
    simp only [map_add, Submodule.coe_add]
    module
  map_smul' scalar state := by
    apply Subtype.ext
    simp only [map_smul, Submodule.coe_smul, RingHom.id_apply]
    module

def wPairing : LinearMap.BilinForm ℂ NativeW :=
  tensorPairing.compl₁₂ (oddTarget data determinantUnit).subtype
    (oddTarget data determinantUnit).subtype

theorem w_pairing_symm : wPairing.IsSymm := by
  constructor
  intro first second
  exact tensor_pairing_symm.eq _ _

theorem odd_projection_pairing (first : NativeW) (second : NativeTensor) :
    tensorPairing first.val (oddProjection second).val = tensorPairing first.val second := by
  have odd := (mem_oddTarget data determinantUnit first.val).mp first.property
  have equation := tensor_theta_adjoint first.val second
  rw [odd, map_neg, LinearMap.neg_apply] at equation
  change tensorPairing first.val ((2 : ℂ)⁻¹ •
    (second - sigmaTensor data determinantUnit second)) = _
  rw [map_smul, map_sub, smul_eq_mul, ← equation]
  ring

theorem w_pairing_nondegenerate
    (H : Matrix (Fin data.rank) (Fin data.rank) ℂ)
    (leftInverse : H * gramComplex data = 1)
    (rightInverse : gramComplex data * H = 1) : wPairing.Nondegenerate := by
  have separation := tensor_pairing_nondegenerate H leftInverse rightInverse
  have leftSeparating : wPairing.SeparatingLeft := by
    intro state radical
    apply Subtype.ext
    apply separation.1
    intro other
    rw [← odd_projection_pairing state other]
    exact radical (oddProjection other)
  constructor
  · exact leftSeparating
  · intro state radical
    apply leftSeparating
    intro other
    rw [w_pairing_symm.eq]
    exact radical other

theorem theta_opposite_orthogonal (first second : NativeTensor)
    (odd : sigmaTensor data determinantUnit first = -first)
    (even : sigmaTensor data determinantUnit second = second) :
    tensorPairing first second = 0 := by
  have equation := tensor_theta_adjoint first second
  rw [odd, even, map_neg, LinearMap.neg_apply] at equation
  linear_combination -(1 / 2 : ℂ) * equation

end
end D5.S3.VertexAlgebra.LatticeHalfFockBpZ
