/- GID: D5/S3/VertexAlgebra/LatticeBcGhostAuxiliarySelection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostAuxiliarySelection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual rotated tensor auxiliary selection and inserted two-slot cancellation.
-/

import D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm
import D5.S3.VertexAlgebra.LatticeFockAuxiliarySelection
import D5.S3.VertexAlgebra.LatticeBcGhostPerturbationTermination

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.LatticeBcGhostAuxiliarySelection

open LatticeGeneratingFieldLocality LatticeBcGhostBrstCharge LatticeSugawaraCurrents
  LatticeFiniteNegativeGeneration LatticeChargedFockForms LatticeOscillatorFockForm
  OriginalQQuartetSource BcGhostFockSupport BcGhostBpZForm BcGhostRotatedForm
  LatticeBcGhostHermitianForm LatticeFockAuxiliarySelection
open scoped BigOperators TensorProduct

noncomputable section

section RealFrame

variable (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
variable (xReal : ∀ axis, star (frame xAxis axis) = frame xAxis axis)
variable (yReal : ∀ axis, star (frame yAxis axis) = frame yAxis axis)
variable (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
variable (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)

include distinct xReal yReal xDual yDual in
theorem F_factor_selection (leftCharge rightCharge : Charge D)
    (left right : Oscillator D) (leftGhost rightGhost : Fock ℂ)
    (leftMatterDegree rightMatterDegree leftGhostDegree rightGhostDegree : ℤ)
    (leftMatterHomogeneous : MvPolynomial.IsWeightedHomogeneous
      (auxiliaryWeight D xAxis yAxis) left leftMatterDegree)
    (rightMatterHomogeneous : MvPolynomial.IsWeightedHomogeneous
      (auxiliaryWeight D xAxis yAxis) right rightMatterDegree)
    (leftGhostHomogeneous : HomogeneousDegree leftGhostDegree leftGhost)
    (rightGhostHomogeneous : HomogeneousDegree rightGhostDegree rightGhost)
    (mismatch : (leftMatterDegree + leftGhostDegree - 1) +
      (rightMatterDegree + rightGhostDegree - 1) ≠ 1) :
    F D (Finsupp.single leftCharge (coordinateSub D frame left) ⊗ₜ[ℂ] leftGhost)
      (Finsupp.single rightCharge (coordinateSub D frame right) ⊗ₜ[ℂ] rightGhost) = 0 := by
  classical
  rw [F_tmul, hermitian_single]
  by_cases ghostMatch : leftGhostDegree + rightGhostDegree = 3
  · have matterZero := fockForm_auxiliary_selection D frame xAxis yAxis distinct
      xReal yReal xDual yDual left right leftMatterDegree rightMatterDegree
      leftMatterHomogeneous rightMatterHomogeneous (by omega)
    simp [matterZero]
  · rw [Hplus_degree_selection leftGhostDegree rightGhostDegree leftGhost rightGhost
      leftGhostHomogeneous rightGhostHomogeneous ghostMatch, mul_zero]

include distinct xReal yReal xDual yDual in
theorem F_c0_factor_selection (leftCharge rightCharge : Charge D)
    (left right : Oscillator D) (leftGhost rightGhost : Fock ℂ)
    (leftMatterDegree rightMatterDegree leftGhostDegree rightGhostDegree : ℤ)
    (leftMatterHomogeneous : MvPolynomial.IsWeightedHomogeneous
      (auxiliaryWeight D xAxis yAxis) left leftMatterDegree)
    (rightMatterHomogeneous : MvPolynomial.IsWeightedHomogeneous
      (auxiliaryWeight D xAxis yAxis) right rightMatterDegree)
    (leftGhostHomogeneous : HomogeneousDegree leftGhostDegree leftGhost)
    (rightGhostHomogeneous : HomogeneousDegree rightGhostDegree rightGhost)
    (mismatch : (leftMatterDegree + leftGhostDegree - 1) +
      (rightMatterDegree + rightGhostDegree - 1) ≠ 0) :
    F D (Finsupp.single leftCharge (coordinateSub D frame left) ⊗ₜ[ℂ] leftGhost)
      (C D 0 (Finsupp.single rightCharge (coordinateSub D frame right) ⊗ₜ[ℂ] rightGhost)) = 0 := by
  classical
  simp only [C, TensorProduct.map_tmul, LinearMap.id_apply, F_tmul, hermitian_single]
  by_cases ghostMatch : leftGhostDegree + rightGhostDegree = 2
  · have matterZero := fockForm_auxiliary_selection D frame xAxis yAxis distinct
      xReal yReal xDual yDual left right leftMatterDegree rightMatterDegree
      leftMatterHomogeneous rightMatterHomogeneous (by omega)
    simp [matterZero]
  · rw [Hplus_c0_degree_selection leftGhostDegree rightGhostDegree leftGhost rightGhost
      leftGhostHomogeneous rightGhostHomogeneous ghostMatch, mul_zero]

private theorem downWord_degree (subset : Finset ℕ) :
    HomogeneousDegree
      (1 + epsilonCount subset + (thetaCount subset : ℤ) - (etaCount subset : ℤ))
      (downWord subset down) := by
  exact (BcGhostRelativeForm.homogeneous_eigenvalue _ _).mpr (polarized_J subset)

include distinct xReal yReal xDual yDual in
theorem F_nativeWord_selection (leftCharge rightCharge : Charge D)
    (left right : NativeIndex D)
    (mismatch : nativeDegree D xAxis yAxis left.1 left.2 +
      nativeDegree D xAxis yAxis right.1 right.2 ≠ 1) :
    F D (nativeWord D frame leftCharge left) (nativeWord D frame rightCharge right) = 0 := by
  apply F_factor_selection D frame xAxis yAxis distinct xReal yReal xDual yDual
    leftCharge rightCharge (MvPolynomial.monomial left.1 1) (MvPolynomial.monomial right.1 1)
    (downWord left.2 down) (downWord right.2 down)
    (Finsupp.weight (auxiliaryWeight D xAxis yAxis) left.1)
    (Finsupp.weight (auxiliaryWeight D xAxis yAxis) right.1)
    (1 + epsilonCount left.2 + (thetaCount left.2 : ℤ) - (etaCount left.2 : ℤ))
    (1 + epsilonCount right.2 + (thetaCount right.2 : ℤ) - (etaCount right.2 : ℤ))
    (MvPolynomial.isWeightedHomogeneous_monomial _ _ _ rfl)
    (MvPolynomial.isWeightedHomogeneous_monomial _ _ _ rfl)
    (downWord_degree left.2) (downWord_degree right.2)
  unfold nativeDegree at mismatch
  omega

include distinct xReal yReal xDual yDual in
theorem F_c0_nativeWord_selection (leftCharge rightCharge : Charge D)
    (left right : NativeIndex D)
    (mismatch : nativeDegree D xAxis yAxis left.1 left.2 +
      nativeDegree D xAxis yAxis right.1 right.2 ≠ 0) :
    F D (nativeWord D frame leftCharge left) (C D 0 (nativeWord D frame rightCharge right)) = 0 := by
  apply F_c0_factor_selection D frame xAxis yAxis distinct xReal yReal xDual yDual
    leftCharge rightCharge (MvPolynomial.monomial left.1 1) (MvPolynomial.monomial right.1 1)
    (downWord left.2 down) (downWord right.2 down)
    (Finsupp.weight (auxiliaryWeight D xAxis yAxis) left.1)
    (Finsupp.weight (auxiliaryWeight D xAxis yAxis) right.1)
    (1 + epsilonCount left.2 + (thetaCount left.2 : ℤ) - (etaCount left.2 : ℤ))
    (1 + epsilonCount right.2 + (thetaCount right.2 : ℤ) - (etaCount right.2 : ℤ))
    (MvPolynomial.isWeightedHomogeneous_monomial _ _ _ rfl)
    (MvPolynomial.isWeightedHomogeneous_monomial _ _ _ rfl)
    (downWord_degree left.2) (downWord_degree right.2)
  unfold nativeDegree at mismatch
  omega

private theorem finite_pairing (operator : Module.End ℂ (State D))
    (leftCharge rightCharge : Charge D) (left right : Finset (NativeIndex D))
    (leftCoefficients rightCoefficients : NativeIndex D → ℂ) :
    F D (∑ index ∈ left, leftCoefficients index • nativeWord D frame leftCharge index)
      (operator (∑ index ∈ right, rightCoefficients index • nativeWord D frame rightCharge index)) =
      ∑ first ∈ left, ∑ second ∈ right,
        star (leftCoefficients first) * rightCoefficients second *
          F D (nativeWord D frame leftCharge first) (operator (nativeWord D frame rightCharge second)) := by
  simp [F, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first firstMember
  apply Finset.sum_congr rfl
  intro second secondMember
  ring

include distinct xReal yReal xDual yDual in
theorem F_nativeCoefficients_selection
    (inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (leftCharge rightCharge : Charge D) (left right : State D)
    (leftSector : chargeProjection D leftCharge left = left)
    (rightSector : chargeProjection D rightCharge right = right)
    (mismatch : ∀ first ∈ (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse leftCharge left).support,
      ∀ second ∈ (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse rightCharge right).support,
      nativeDegree D xAxis yAxis first.1 first.2 + nativeDegree D xAxis yAxis second.1 second.2 ≠ 1) :
    F D left right = 0 := by
  classical
  have expansion := finite_pairing D frame (1 : Module.End ℂ (State D)) leftCharge rightCharge
    (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse leftCharge left).support
    (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse rightCharge right).support
    (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse leftCharge left)
    (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse rightCharge right)
  rw [native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse leftCharge left leftSector,
    native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse rightCharge right rightSector] at expansion
  rw [show F D left right = _ from expansion]
  apply Finset.sum_eq_zero
  intro first firstMember
  apply Finset.sum_eq_zero
  intro second secondMember
  simp only [Module.End.one_apply]
  rw [F_nativeWord_selection D frame xAxis yAxis distinct xReal yReal xDual yDual
    leftCharge rightCharge first second (mismatch first firstMember second secondMember), mul_zero]

include distinct xReal yReal xDual yDual in
theorem F_c0_nativeCoefficients_selection
    (inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (leftCharge rightCharge : Charge D) (left right : State D)
    (leftSector : chargeProjection D leftCharge left = left)
    (rightSector : chargeProjection D rightCharge right = right)
    (mismatch : ∀ first ∈ (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse leftCharge left).support,
      ∀ second ∈ (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse rightCharge right).support,
      nativeDegree D xAxis yAxis first.1 first.2 + nativeDegree D xAxis yAxis second.1 second.2 ≠ 0) :
    F D left (C D 0 right) = 0 := by
  classical
  have expansion := finite_pairing D frame (C D 0) leftCharge rightCharge
    (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse leftCharge left).support
    (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse rightCharge right).support
    (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse leftCharge left)
    (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse rightCharge right)
  rw [native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse leftCharge left leftSector,
    native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse rightCharge right rightSector] at expansion
  rw [expansion]
  apply Finset.sum_eq_zero
  intro first firstMember
  apply Finset.sum_eq_zero
  intro second secondMember
  rw [F_c0_nativeWord_selection D frame xAxis yAxis distinct xReal yReal xDual yDual
    leftCharge rightCharge first second (mismatch first firstMember second secondMember), mul_zero]

private theorem pairing_span (operator : Module.End ℂ (State D))
    (leftSet rightSet : Set (State D))
    (vanishing : ∀ left ∈ leftSet, ∀ right ∈ rightSet, F D left (operator right) = 0)
    (left right : State D) (leftMember : left ∈ Submodule.span ℂ leftSet)
    (rightMember : right ∈ Submodule.span ℂ rightSet) : F D left (operator right) = 0 := by
  induction leftMember using Submodule.span_induction with
  | mem left leftMember =>
    induction rightMember using Submodule.span_induction with
    | mem right rightMember => exact vanishing left leftMember right rightMember
    | zero => simp [F]
    | add first second firstMember secondMember firstProof secondProof =>
      simpa [F, map_add] using congrArg₂ (· + ·) firstProof secondProof
    | smul scalar state member inductionHypothesis =>
      change tensorForm D left (operator state) = 0 at inductionHypothesis
      simp only [F, map_smul, inductionHypothesis, smul_zero]
  | zero => simp [F]
  | add first second firstMember secondMember firstProof secondProof =>
    simpa [F, map_add, LinearMap.add_apply] using congrArg₂ (· + ·) firstProof secondProof
  | smul scalar state member inductionHypothesis =>
    change tensorForm D state (operator right) = 0 at inductionHypothesis
    simp only [F, map_smulₛₗ, LinearMap.smul_apply, inductionHypothesis, smul_zero]

include distinct xReal yReal xDual yDual in
theorem F_signedEnergyFiltration_vanishing (leftCharge rightCharge : Charge D)
    (leftLevel rightLevel lowerL lowerR : ℤ) (above : 1 < lowerL + lowerR)
    (left right : State D)
    (leftMember : left ∈ signedEnergyFiltration D frame leftCharge xAxis yAxis leftLevel lowerL)
    (rightMember : right ∈ signedEnergyFiltration D frame rightCharge xAxis yAxis rightLevel lowerR) :
    F D left right = 0 := by
  apply pairing_span D (1 : Module.End ℂ (State D)) _ _ _ left right leftMember rightMember
  rintro _ ⟨first, firstMember, rfl⟩ _ ⟨second, secondMember, rfl⟩
  have firstBound : lowerL ≤ nativeDegree D xAxis yAxis first.1 first.2 := firstMember.2
  have secondBound : lowerR ≤ nativeDegree D xAxis yAxis second.1 second.2 := secondMember.2
  exact F_nativeWord_selection D frame xAxis yAxis distinct xReal yReal xDual yDual
    leftCharge rightCharge first second (by omega)

include distinct xReal yReal xDual yDual in
theorem F_c0_signedEnergyFiltration_vanishing (leftCharge rightCharge : Charge D)
    (leftLevel rightLevel lowerL lowerR : ℤ) (above : 0 < lowerL + lowerR)
    (left right : State D)
    (leftMember : left ∈ signedEnergyFiltration D frame leftCharge xAxis yAxis leftLevel lowerL)
    (rightMember : right ∈ signedEnergyFiltration D frame rightCharge xAxis yAxis rightLevel lowerR) :
    F D left (C D 0 right) = 0 := by
  apply pairing_span D (C D 0) _ _ _ left right leftMember rightMember
  rintro _ ⟨first, firstMember, rfl⟩ _ ⟨second, secondMember, rfl⟩
  have firstBound : lowerL ≤ nativeDegree D xAxis yAxis first.1 first.2 := firstMember.2
  have secondBound : lowerR ≤ nativeDegree D xAxis yAxis second.1 second.2 := secondMember.2
  exact F_c0_nativeWord_selection D frame xAxis yAxis distinct xReal yReal xDual yDual
    leftCharge rightCharge first second (by omega)

include distinct xReal yReal xDual yDual in
theorem F_c0_two_slot_cancellation (leftCharge rightCharge : Charge D)
    (leftLevel rightLevel : ℤ) (leftBase rightBase leftTail rightTail : State D)
    (leftBaseMember : leftBase ∈ signedEnergyFiltration D frame leftCharge xAxis yAxis leftLevel 0)
    (rightBaseMember : rightBase ∈ signedEnergyFiltration D frame rightCharge xAxis yAxis rightLevel 0)
    (leftTailMember : leftTail ∈ signedEnergyFiltration D frame leftCharge xAxis yAxis leftLevel 1)
    (rightTailMember : rightTail ∈ signedEnergyFiltration D frame rightCharge xAxis yAxis rightLevel 1) :
    F D (leftBase + leftTail) (C D 0 (rightBase + rightTail)) = F D leftBase (C D 0 rightBase) := by
  have baseTail := F_c0_signedEnergyFiltration_vanishing D frame xAxis yAxis distinct
    xReal yReal xDual yDual leftCharge rightCharge leftLevel rightLevel 0 1 (by norm_num)
    leftBase rightTail leftBaseMember rightTailMember
  have tailBase := F_c0_signedEnergyFiltration_vanishing D frame xAxis yAxis distinct
    xReal yReal xDual yDual leftCharge rightCharge leftLevel rightLevel 1 0 (by norm_num)
    leftTail rightBase leftTailMember rightBaseMember
  have tailTail := F_c0_signedEnergyFiltration_vanishing D frame xAxis yAxis distinct
    xReal yReal xDual yDual leftCharge rightCharge leftLevel rightLevel 1 1 (by norm_num)
    leftTail rightTail leftTailMember rightTailMember
  change tensorForm D (leftBase + leftTail) (C D 0 (rightBase + rightTail)) = _
  simp only [map_add, LinearMap.add_apply]
  change F D leftBase (C D 0 rightBase) + F D leftTail (C D 0 rightBase) +
    (F D leftBase (C D 0 rightTail) + F D leftTail (C D 0 rightTail)) = _
  rw [baseTail, tailBase, tailTail]
  simp

end RealFrame

theorem F_c0_down_normalization (D : LatticeData) (left right : Carrier D) :
    F D (left ⊗ₜ[ℂ] down) (C D 0 (right ⊗ₜ[ℂ] down)) = -hermitianForm D left right := by
  have downEqual : down = j := down_original_basis
  have upEqual : c 0 down = k := up_original_basis
  rw [C, TensorProduct.map_tmul, LinearMap.id_apply, F_tmul, upEqual, downEqual,
    Hplus_j_k, mul_neg_one]

theorem F_c0_native_empty_normalization (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (leftCharge rightCharge : Charge D)
    (leftPowers rightPowers : Index D →₀ ℕ) :
    F D (nativeWord D frame leftCharge (leftPowers, ∅))
      (C D 0 (nativeWord D frame rightCharge (rightPowers, ∅))) =
      -(if leftCharge = rightCharge then
        fockForm D (coordinateSub D frame (MvPolynomial.monomial leftPowers 1))
          (coordinateSub D frame (MvPolynomial.monomial rightPowers 1)) else 0) := by
  classical
  simp only [nativeWord, downWord, Finset.sort_empty, List.map_nil, List.prod_nil,
    Module.End.one_apply]
  rw [F_c0_down_normalization, hermitian_single]

theorem F_c0_native_two_slot_normalization (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xReal : ∀ axis, star (frame xAxis axis) = frame xAxis axis)
    (yReal : ∀ axis, star (frame yAxis axis) = frame yAxis axis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (leftCharge rightCharge : Charge D) (leftPowers rightPowers : Index D →₀ ℕ)
    (leftDegree : 0 ≤ Finsupp.weight (auxiliaryWeight D xAxis yAxis) leftPowers)
    (rightDegree : 0 ≤ Finsupp.weight (auxiliaryWeight D xAxis yAxis) rightPowers)
    (leftTail rightTail : State D)
    (leftTailMember : leftTail ∈ signedEnergyFiltration D frame leftCharge xAxis yAxis
      (nativeLevel D leftPowers ∅) 1)
    (rightTailMember : rightTail ∈ signedEnergyFiltration D frame rightCharge xAxis yAxis
      (nativeLevel D rightPowers ∅) 1) :
    F D (nativeWord D frame leftCharge (leftPowers, ∅) + leftTail)
      (C D 0 (nativeWord D frame rightCharge (rightPowers, ∅) + rightTail)) =
      -(if leftCharge = rightCharge then
        fockForm D (coordinateSub D frame (MvPolynomial.monomial leftPowers 1))
          (coordinateSub D frame (MvPolynomial.monomial rightPowers 1)) else 0) := by
  classical
  have leftBase : nativeWord D frame leftCharge (leftPowers, ∅) ∈
      signedEnergyFiltration D frame leftCharge xAxis yAxis (nativeLevel D leftPowers ∅) 0 := by
    apply Submodule.subset_span
    refine ⟨(leftPowers, ∅), ⟨rfl, ?_⟩, rfl⟩
    simpa [nativeDegree, epsilonCount, thetaCount, etaCount] using leftDegree
  have rightBase : nativeWord D frame rightCharge (rightPowers, ∅) ∈
      signedEnergyFiltration D frame rightCharge xAxis yAxis (nativeLevel D rightPowers ∅) 0 := by
    apply Submodule.subset_span
    refine ⟨(rightPowers, ∅), ⟨rfl, ?_⟩, rfl⟩
    simpa [nativeDegree, epsilonCount, thetaCount, etaCount] using rightDegree
  rw [F_c0_two_slot_cancellation D frame xAxis yAxis distinct xReal yReal xDual yDual
    leftCharge rightCharge (nativeLevel D leftPowers ∅) (nativeLevel D rightPowers ∅)
    _ _ leftTail rightTail leftBase rightBase leftTailMember rightTailMember]
  exact F_c0_native_empty_normalization D frame leftCharge rightCharge leftPowers rightPowers

#print axioms F_factor_selection
#print axioms F_c0_factor_selection
#print axioms F_nativeWord_selection
#print axioms F_c0_nativeWord_selection
#print axioms F_nativeCoefficients_selection
#print axioms F_c0_nativeCoefficients_selection
#print axioms F_signedEnergyFiltration_vanishing
#print axioms F_c0_signedEnergyFiltration_vanishing
#print axioms F_c0_two_slot_cancellation
#print axioms F_c0_down_normalization
#print axioms F_c0_native_empty_normalization
#print axioms F_c0_native_two_slot_normalization

end
end D5.S3.VertexAlgebra.LatticeBcGhostAuxiliarySelection
