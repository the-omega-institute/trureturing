/- GID: D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Charged
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockBpZ/Charged
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite integer coefficient reindexing gives the original charged BPZ adjoint. -/

import D5.S3.VertexAlgebra.LatticeHalfFockBpZ.Transpose
import D5.S3.VertexAlgebra.LatticeHalfFockBpZ.Tensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockBpZ

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients MvPolynomial
open GolayLeech.ExplicitLeechLattice TwistedGround.NativeSymmetricForm
open TwistedGround.NativeHyperbolicActions
open scoped BigOperators TensorProduct

noncomputable section

private theorem translation_finite_expansion (D : LatticeData) (charge : Charge D)
    (degree : ℤ) (polynomial : Oscillator D) :
    halfTranslationCoeff D charge degree polynomial =
      ∑ index ∈ (halfTranslatedPolynomial D charge polynomial).support,
        if (index : ℤ) = degree then
          (halfTranslatedPolynomial D charge polynomial).coeff index else 0 := by
  classical
  by_cases negative : degree < 0
  · simp [halfTranslationCoeff, negative, show ∀ index : ℕ, ¬(index : ℤ) = degree by omega]
  · rw [halfTranslationCoeff, if_neg negative]
    symm
    calc
      _ = if (degree.toNat : ℤ) = degree then
          (halfTranslatedPolynomial D charge polynomial).coeff degree.toNat else 0 := by
        apply Finset.sum_eq_single degree.toNat
        · intro index membership unequal
          rw [if_neg (by omega)]
        · intro absent
          have coefficientZero := Polynomial.notMem_support_iff.mp absent
          simp [coefficientZero]
      _ = _ := by rw [if_pos (by omega)]

private theorem oscillator_pairing_finite_expansion (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (first second : Oscillator D) :
    oscillatorPairing D (oscillatorCoefficient D charge exponent first) second =
      ∑ firstDegree ∈ (halfTranslatedPolynomial D charge first).support,
        ∑ secondDegree ∈ (halfTranslatedPolynomial D charge second).support,
          if (secondDegree : ℤ) = exponent + chargeNorm D charge + firstDegree then
            oscillatorPairing D
              ((halfTranslatedPolynomial D charge first).coeff firstDegree)
              ((halfTranslatedPolynomial D charge second).coeff secondDegree) else 0 := by
  classical
  change oscillatorPairing D (∑ᶠ degree : ℕ,
    oscillatorTerm D charge exponent first degree) second = _
  rw [finsum_eq_sum_of_support_subset _ (term_support D charge exponent first),
    map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro degree membership
  unfold oscillatorTerm
  rw [mul_comm, half_creation_multiplication_transpose, translation_finite_expansion, map_sum]
  apply Finset.sum_congr rfl
  intro index membership
  split_ifs <;> simp

theorem oscillator_charged_transpose (D : LatticeData) (charge : Charge D) (exponent : ℤ)
    (first second : Oscillator D) :
    oscillatorPairing D (oscillatorCoefficient D charge exponent first) second =
      oscillatorPairing D first
        (oscillatorCoefficient D charge (-2 * chargeNorm D charge - exponent) second) := by
  classical
  rw [oscillator_pairing_finite_expansion, (oscillator_pairing_symm D).eq first,
    oscillator_pairing_finite_expansion]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro firstDegree firstMembership
  apply Finset.sum_congr rfl
  intro secondDegree secondMembership
  have indices : (secondDegree : ℤ) = exponent + chargeNorm D charge + firstDegree ↔
      (firstDegree : ℤ) = -2 * chargeNorm D charge - exponent +
        chargeNorm D charge + secondDegree := by omega
  by_cases diagonal : (secondDegree : ℤ) = exponent + chargeNorm D charge + firstDegree
  · rw [if_pos diagonal, if_pos (indices.mp diagonal)]
    exact (oscillator_pairing_symm D).eq _ _
  · rw [if_neg diagonal, if_neg (mt indices.mpr diagonal)]

theorem tensor_charged_adjoint (charge : Charge data) (exponent : ℤ)
    (first second : ActualTensor data determinantUnit) :
    tensorPairing (chargedCoefficient data determinantUnit charge exponent first) second =
      chargeScalar data charge * tensorPairing first
        (TensorProduct.map
          (oscillatorCoefficient data charge (-2 * chargeNorm data charge - exponent))
          (epsilon data charge (-charge) • groundAction data determinantUnit (-charge)) second) := by
  induction first using TensorProduct.induction_on with
  | zero => simp
  | tmul polynomial ground =>
    induction second using TensorProduct.induction_on with
    | zero => simp
    | tmul other otherGround =>
      simp only [chargedCoefficient, LinearMap.smul_apply, TensorProduct.map_tmul,
        map_smul, tensor_pairing_tmul, oscillator_charged_transpose, original_integral_adjoint]
      simp only [smul_eq_mul]
      all_goals ring
    | add firstSecond secondSecond firstProof secondProof =>
      simp only [map_add, mul_add, firstProof, secondProof]
  | add firstFirst secondFirst firstProof secondProof =>
    simp only [map_add, LinearMap.add_apply, mul_add, firstProof, secondProof]

end
end D5.S3.VertexAlgebra.LatticeHalfFockBpZ
