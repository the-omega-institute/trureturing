/- GID: D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockSugawaraHermitian
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockSugawaraHermitian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original finite-support half Sugawara and chosen-ground tensor adjoints. -/

import D5.S3.VertexAlgebra.HalfFock.Hermitian.LatticeHalfFockTensorHermitian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockSugawaraHermitian

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeHalfFock
open LatticeHalfFockHermitian LatticeHalfFockTensorHermitian
open LatticeHalfFockChargedTensorCoefficients
open scoped BigOperators TensorProduct

noncomputable section

theorem normalPair_adjoint (D : LatticeData) (first second : Fin D.rank)
    (firstMode secondMode : ℤ) (left right : Oscillator D) :
    halfForm D (normalPair D first second firstMode secondMode left) right =
      halfForm D left (normalPair D first second (-firstMode - 1) (-secondMode - 1) right) := by
  by_cases negative : firstMode < 0
  · have opposite : ¬ -firstMode - 1 < 0 := by omega
    simp only [normalPair, if_pos negative, if_neg opposite, Module.End.mul_apply]
    rw [halfForm_current_adjoint, halfForm_current_adjoint]
  · have opposite : -firstMode - 1 < 0 := by omega
    simp only [normalPair, if_neg negative, if_pos opposite, Module.End.mul_apply]
    rw [halfForm_current_adjoint, halfForm_current_adjoint]

theorem normalSum_adjoint (D : LatticeData) (first second : Fin D.rank)
    (mode : ℤ) (left right : Oscillator D) :
    halfForm D (normalSum D first second mode left) right =
      halfForm D left (normalSum D first second (-mode) right) := by
  classical
  let radius : ℤ := max (bound D left : ℤ) (bound D right : ℤ) + mode.natAbs + 2
  have leftBound := le_max_left (bound D left : ℤ) (bound D right : ℤ)
  have rightBound := le_max_right (bound D left : ℤ) (bound D right : ℤ)
  have upperMode : mode ≤ (mode.natAbs : ℤ) := Int.le_natAbs
  have lowerMode : -mode ≤ (mode.natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs : -mode ≤ ((-mode).natAbs : ℤ))
  have leftLower : -radius ≤ min (mode - bound D left) 0 := by dsimp [radius]; omega
  have rightLower : -radius ≤ min (-mode - bound D right) 0 := by dsimp [radius]; omega
  have leftUpper : (bound D left : ℤ) - 1 ≤ radius - 1 := by dsimp [radius]; omega
  have rightUpper : (bound D right : ℤ) - 1 ≤ radius - 1 := by dsimp [radius]; omega
  rw [normalSum_interval D first second mode left (-radius) (radius - 1) leftLower leftUpper,
    normalSum_interval D first second (-mode) right (-radius) (radius - 1) rightLower rightUpper]
  simp only [map_sum, LinearMap.sum_apply]
  simp_rw [normalPair_adjoint]
  apply Finset.sum_bij (fun index _ => -index - 1)
  · intro index member
    simp only [Finset.mem_Icc] at member ⊢
    omega
  · intro firstIndex memberFirst secondIndex memberSecond equality
    omega
  · intro index member
    refine ⟨-index - 1, ?_, by omega⟩
    simp only [Finset.mem_Icc] at member ⊢
    omega
  · intro index member
    rw [show -(mode - index - 1) - 1 = -mode - (-index - 1) - 1 by omega]

end
end D5.S3.VertexAlgebra.LatticeHalfFockSugawaraHermitian
