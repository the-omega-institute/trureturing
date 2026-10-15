/- GID: D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Stress
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockBpZ/Stress
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual half-Fock stress reflection and native spectral orthogonality. -/

import D5.S3.VertexAlgebra.LatticeHalfFockBpZ.Tensor

set_option autoImplicit false
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockBpZ

open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockNativeSpectrum
open LatticeHalfFockChargedTensorCoefficients GolayLeech.ExplicitLeechLattice
open TwistedGround.NativeHyperbolicActions
open scoped BigOperators TensorProduct

noncomputable section

theorem oscillator_pair_adjoint (D : LatticeData) (firstAxis secondAxis : Fin D.rank)
    (firstMode secondMode : ℤ) (first second : Oscillator D) :
    oscillatorPairing D (normalPair D firstAxis secondAxis firstMode secondMode first) second =
      oscillatorPairing D first
        (normalPair D firstAxis secondAxis (-firstMode - 1) (-secondMode - 1) second) := by
  by_cases negative : firstMode < 0
  · have reflected : ¬ -firstMode - 1 < 0 := by omega
    simp only [normalPair, if_pos negative, if_neg reflected, Module.End.mul_apply]
    rw [oscillator_current_adjoint, oscillator_current_adjoint, neg_neg]
  · have reflected : -firstMode - 1 < 0 := by omega
    simp only [normalPair, if_neg negative, if_pos reflected, Module.End.mul_apply]
    rw [oscillator_current_adjoint, oscillator_current_adjoint, neg_neg]

theorem oscillator_normal_sum_adjoint (D : LatticeData)
    (firstAxis secondAxis : Fin D.rank) (mode : ℤ) (first second : Oscillator D) :
    oscillatorPairing D (normalSum D firstAxis secondAxis mode first) second =
      oscillatorPairing D first (normalSum D firstAxis secondAxis (-mode) second) := by
  let reflected : ℤ ≃ ℤ := {
    toFun := fun index => -index - 1
    invFun := fun index => -index - 1
    left_inv := by intro index; dsimp; omega
    right_inv := by intro index; dsimp; omega }
  calc
    oscillatorPairing D (normalSum D firstAxis secondAxis mode first) second =
        ∑ᶠ index : ℤ, oscillatorPairing D
          (normalPair D firstAxis secondAxis index (mode - index - 1) first) second := by
      exact map_finsum ((oscillatorPairing D).flip second)
        (normalPair_finite D firstAxis secondAxis mode first)
    _ = ∑ᶠ index : ℤ, oscillatorPairing D first
        (normalPair D firstAxis secondAxis (reflected index)
          (-mode - reflected index - 1) second) := by
      apply finsum_congr
      intro index
      change oscillatorPairing D
        (normalPair D firstAxis secondAxis index (mode - index - 1) first) second =
        oscillatorPairing D first (normalPair D firstAxis secondAxis
          (-index - 1) (-mode - (-index - 1) - 1) second)
      rw [oscillator_pair_adjoint]
      rw [show -(mode - index - 1) - 1 = -mode - (-index - 1) - 1 by omega]
    _ = ∑ᶠ index : ℤ, oscillatorPairing D first
        (normalPair D firstAxis secondAxis index (-mode - index - 1) second) :=
      finsum_comp_equiv reflected (f := fun index : ℤ => oscillatorPairing D first
        (normalPair D firstAxis secondAxis index (-mode - index - 1) second))
    _ = oscillatorPairing D first (normalSum D firstAxis secondAxis (-mode) second) :=
      (map_finsum (oscillatorPairing D first)
        (normalPair_finite D firstAxis secondAxis (-mode) second)).symm

theorem oscillator_stress_adjoint (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (mode : ℤ)
    (first second : Oscillator D) :
    oscillatorPairing D (L D H mode first) second =
      oscillatorPairing D first (L D H (-mode) second) := by
  simp only [L, rawL, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, Module.End.one_apply, map_add, map_sum, map_smul,
    oscillator_normal_sum_adjoint, smul_eq_mul]
  congr 1
  simp only [neg_eq_zero]

theorem tensor_stress_adjoint (H : Matrix (Fin data.rank) (Fin data.rank) ℂ)
    (mode : ℤ) (first second : NativeTensor) :
    tensorPairing (tensorL data (ActualGround data determinantUnit) H mode first) second =
      tensorPairing first (tensorL data (ActualGround data determinantUnit) H (-mode) second) := by
  induction first using TensorProduct.induction_on with
  | zero => simp
  | tmul first ground =>
    induction second using TensorProduct.induction_on with
    | zero => simp
    | tmul second other =>
      change tensorPairing ((L data H mode first) ⊗ₜ[ℂ] ground) (second ⊗ₜ[ℂ] other) =
        tensorPairing (first ⊗ₜ[ℂ] ground) ((L data H (-mode) second) ⊗ₜ[ℂ] other)
      rw [tensor_pairing_tmul, tensor_pairing_tmul, oscillator_stress_adjoint]
    | add first second firstProof secondProof =>
      simp only [map_add, firstProof, secondProof]
  | add first second firstProof secondProof =>
    simp only [map_add, LinearMap.add_apply, firstProof, secondProof]

theorem native_grade_orthogonal (H : Matrix (Fin data.rank) (Fin data.rank) ℂ)
    (firstValue secondValue : ℂ) (different : firstValue ≠ secondValue)
    (first second : NativeTensor)
    (firstEigen : first ∈ eigenspace data determinantUnit H firstValue)
    (secondEigen : second ∈ eigenspace data determinantUnit H secondValue) :
    tensorPairing first second = 0 := by
  have firstEquation : nativeL0 data determinantUnit H first = firstValue • first := by
    exact sub_eq_zero.mp firstEigen
  have secondEquation : nativeL0 data determinantUnit H second = secondValue • second := by
    exact sub_eq_zero.mp secondEigen
  have adjoint := tensor_stress_adjoint H 0 first second
  change tensorPairing (nativeL0 data determinantUnit H first) second =
    tensorPairing first (nativeL0 data determinantUnit H second) at adjoint
  rw [firstEquation, secondEquation, map_smul, LinearMap.smul_apply, map_smul,
    smul_eq_mul, smul_eq_mul] at adjoint
  exact (mul_eq_zero.mp (by linear_combination adjoint :
    (firstValue - secondValue) * tensorPairing first second = 0)).resolve_left
      (sub_ne_zero.mpr different)

end
end D5.S3.VertexAlgebra.LatticeHalfFockBpZ
