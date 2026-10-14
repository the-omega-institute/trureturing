/- GID: D5/S3/VertexAlgebra/OriginalQEnergyInclusionPairing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/OriginalQEnergyInclusionPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native finite original-Q inclusion preserves the actual right-C0 pairing.
-/

import D5.S3.VertexAlgebra.OriginalQActualQuotientTransferTransient
import D5.S3.VertexAlgebra.OriginalQTransferredTermComputationTransient
import D5.S3.VertexAlgebra.LatticeBcGhostAuxiliarySelection

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.OriginalQEnergyInclusionPairing

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  LatticeFiniteNegativeGeneration LatticeOscillatorFockForm OriginalQQuartetSource
  LatticeBcGhostHermitianForm LatticeBcGhostAuxiliarySelection BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

variable (D : LatticeData) (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
variable (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
variable (nullDirection : Fin D.rank → ℂ) (xAxis yAxis : Fin D.rank)

local notation "energyP" => (fun beta level => energyProjector D H frame inverse
  leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta xAxis yAxis level)
local notation "energyS" => (fun beta level => energyNormalizer D H frame inverse
  leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level)
local notation "energyQ" => energyOriginalQ D H leftGramInverse rightGramInverse
local notation "energyDelta" => (fun beta level => energyLeading D H leftGramInverse rightGramInverse
  beta nullDirection level)
local notation "inclusion" => (fun beta level => energyReducedInclusion D H frame inverse
  leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level)

theorem energyReducedInclusion_c0_pairing
    (null : gramPair D nullDirection nullDirection = 0) (distinct : xAxis ≠ yAxis)
    (xRow : frame xAxis = nullDirection)
    (xReal : ∀ axis, star (frame xAxis axis) = frame xAxis axis)
    (yReal : ∀ axis, star (frame yAxis axis) = frame yAxis axis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (leftCharge rightCharge : Charge D) (leftLevel rightLevel : ℤ)
    (leftNonzero : chosenP D leftCharge nullDirection ≠ 0)
    (rightNonzero : chosenP D rightCharge nullDirection ≠ 0)
    (leftYRow : frame yAxis = adaptedPartner D leftCharge nullDirection)
    (rightYRow : frame yAxis = adaptedPartner D rightCharge nullDirection)
    (left : LinearMap.range (energyP leftCharge leftLevel))
    (right : LinearMap.range (energyP rightCharge rightLevel)) :
    F D ((inclusion leftCharge leftLevel left : originalEnergySector D H leftCharge leftLevel) : State D)
      (C D 0 ((inclusion rightCharge rightLevel right : originalEnergySector D H rightCharge rightLevel) : State D)) =
      F D left.val.val (C D 0 right.val.val) := by
  classical
  let tail (beta : Charge D) (level : ℤ) (input : LinearMap.range (energyP beta level)) :
      originalEnergySector D H beta level :=
    ∑ steps ∈ (Finset.range (2 * level.toNat + 2)).erase 0,
      ((-(energyS beta level * (energyQ beta level - energyDelta beta level))) ^ steps) input.val
  have expansion (beta : Charge D) (level : ℤ)
      (nonzero : chosenP D beta nullDirection ≠ 0)
      (yRow : frame yAxis = adaptedPartner D beta nullDirection)
      (input : LinearMap.range (energyP beta level)) :
      input.val.val ∈ signedEnergyFiltration D frame beta xAxis yAxis level 0 ∧
      (tail beta level input : State D) ∈ signedEnergyFiltration D frame beta xAxis yAxis level 1 ∧
      ((inclusion beta level input : originalEnergySector D H beta level) : State D) =
        input.val.val + (tail beta level input : State D) := by
    have projectorSquare : energyP beta level * energyP beta level = energyP beta level := by
      apply LinearMap.ext
      intro state
      apply Subtype.ext
      simpa only [Module.End.mul_apply, energyProjector_coe] using LinearMap.congr_fun
        (native_P_idempotent D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis) state.val
    have fixed : energyP beta level input.val = input.val := by
      obtain ⟨preimage, equality⟩ := input.property
      rw [← equality]
      exact LinearMap.congr_fun projectorSquare preimage
    have nativeFixed : P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis input.val.val =
        input.val.val := congrArg (fun state : originalEnergySector D H beta level => state.val) fixed
    have powers (steps : ℕ) :
        (((-(energyS beta level * (energyQ beta level - energyDelta beta level))) ^ steps) input.val : State D) ∈
          signedEnergyFiltration D frame beta xAxis yAxis level (steps : ℤ) := by
      rw [energy_signed_correction_pow_coe]
      have support := original_projected_correction_pow_mem_filtration D H frame inverse
        leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection
        xAxis yAxis null nonzero distinct xRow yRow xDual yDual level input.val.val
        input.val.property.1 input.val.property.2 steps
      rwa [nativeFixed] at support
    have lowerZero : input.val.val ∈ signedEnergyFiltration D frame beta xAxis yAxis level 0 := by
      simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero] using powers 0
    have lowerOne : (tail beta level input : State D) ∈
        signedEnergyFiltration D frame beta xAxis yAxis level 1 := by
      dsimp only [tail]
      rw [Submodule.coe_sum]
      apply Submodule.sum_mem
      intro steps present
      have positive : 1 ≤ (steps : ℤ) := by
        have notZero := (Finset.mem_erase.mp present).1
        omega
      have monotone : signedEnergyFiltration D frame beta xAxis yAxis level (steps : ℤ) ≤
          signedEnergyFiltration D frame beta xAxis yAxis level 1 := by
        apply Submodule.span_le.mpr
        rintro state ⟨index, ⟨atLevel, atDegree⟩, rfl⟩
        exact Submodule.subset_span ⟨index, ⟨atLevel, by omega⟩, rfl⟩
      exact monotone (powers steps)
    have decomposition : inclusion beta level input = input.val + tail beta level input := by
      change energyCorrectionInverse D H frame inverse leftGramInverse rightGramInverse
        leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
        (energyP beta level input.val) = _
      rw [fixed]
      simp only [energyCorrectionInverse, LinearMap.sum_apply]
      have present : 0 ∈ Finset.range (2 * level.toNat + 2) := Finset.mem_range.mpr (by omega)
      exact (Finset.add_sum_erase (Finset.range (2 * level.toNat + 2))
        (fun steps => ((-(energyS beta level * (energyQ beta level - energyDelta beta level))) ^ steps) input.val)
        present).symm.trans (by simp only [pow_zero, Module.End.one_apply]; rfl)
    exact ⟨lowerZero, lowerOne,
      congrArg (fun state : originalEnergySector D H beta level => state.val) decomposition⟩
  obtain ⟨leftBase, leftTail, leftExpansion⟩ := expansion leftCharge leftLevel leftNonzero leftYRow left
  obtain ⟨rightBase, rightTail, rightExpansion⟩ := expansion rightCharge rightLevel rightNonzero rightYRow right
  rw [leftExpansion, rightExpansion]
  exact F_c0_two_slot_cancellation D frame xAxis yAxis distinct xReal yReal xDual yDual
    leftCharge rightCharge leftLevel rightLevel left.val.val right.val.val
    (tail leftCharge leftLevel left) (tail rightCharge rightLevel right)
    leftBase rightBase leftTail rightTail

def energyTransverseDownInput (beta : Charge D) (level : ℤ) (powers : Index D →₀ ℕ)
    (xAbsent : ∀ frequency : ℕ, powers (xAxis, frequency) = 0)
    (yAbsent : ∀ frequency : ℕ, powers (yAxis, frequency) = 0)
    (atLevel : nativeLevel D powers ∅ = level) : LinearMap.range (energyP beta level) := by
  classical
  let state : originalEnergySector D H beta level :=
    ⟨nativeWord D frame beta (powers, ∅), nativeWord_sector D frame beta (powers, ∅), by
      simpa only [atLevel] using nativeWord_T0 D H frame leftGramInverse rightGramInverse beta (powers, ∅)⟩
  refine ⟨state, state, ?_⟩
  apply Subtype.ext
  change P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
    (nativeState D frame beta powers 1 ∅) = nativeState D frame beta powers 1 ∅
  rw [P_native, if_pos ((kappa_zero_iff D xAxis yAxis powers ∅).mpr
    ⟨xAbsent, yAbsent, Finset.empty_subset _⟩), one_smul]

abbrev TransverseDownIndex (D : LatticeData) (xAxis yAxis : Fin D.rank) (level : ℤ) :=
  {powers : Index D →₀ ℕ //
    (∀ frequency : ℕ, powers (xAxis, frequency) = 0) ∧
    (∀ frequency : ℕ, powers (yAxis, frequency) = 0) ∧ nativeLevel D powers ∅ = level}

def energyTransverseDownCombination (beta : Charge D) (level : ℤ)
    (coefficients : TransverseDownIndex D xAxis yAxis level →₀ ℂ) :
    LinearMap.range (energyP beta level) :=
  Finsupp.linearCombination ℂ (fun powers => energyTransverseDownInput D H frame inverse
    leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse xAxis yAxis beta level
    powers.val powers.property.1 powers.property.2.1 powers.property.2.2) coefficients

def transverseDownOscillator (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (xAxis yAxis : Fin D.rank) (level : ℤ)
    (coefficients : TransverseDownIndex D xAxis yAxis level →₀ ℂ) : Oscillator D :=
  Finsupp.linearCombination ℂ
    (fun powers => coordinateSub D frame (MvPolynomial.monomial powers.val 1)) coefficients

theorem energyReducedInclusion_transverse_down_normalization
    (null : gramPair D nullDirection nullDirection = 0) (distinct : xAxis ≠ yAxis)
    (xRow : frame xAxis = nullDirection)
    (xReal : ∀ axis, star (frame xAxis axis) = frame xAxis axis)
    (yReal : ∀ axis, star (frame yAxis axis) = frame yAxis axis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (leftCharge rightCharge : Charge D) (leftLevel rightLevel : ℤ)
    (leftNonzero : chosenP D leftCharge nullDirection ≠ 0)
    (rightNonzero : chosenP D rightCharge nullDirection ≠ 0)
    (leftYRow : frame yAxis = adaptedPartner D leftCharge nullDirection)
    (rightYRow : frame yAxis = adaptedPartner D rightCharge nullDirection)
    (leftCoefficients : TransverseDownIndex D xAxis yAxis leftLevel →₀ ℂ)
    (rightCoefficients : TransverseDownIndex D xAxis yAxis rightLevel →₀ ℂ) :
    F D ((inclusion leftCharge leftLevel (energyTransverseDownCombination D H frame inverse
      leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse xAxis yAxis
      leftCharge leftLevel leftCoefficients)) : State D)
      (C D 0 ((inclusion rightCharge rightLevel (energyTransverseDownCombination D H frame inverse
        leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse xAxis yAxis
        rightCharge rightLevel rightCoefficients)) : State D)) =
      -(if leftCharge = rightCharge then
        fockForm D (transverseDownOscillator D frame xAxis yAxis leftLevel leftCoefficients)
          (transverseDownOscillator D frame xAxis yAxis rightLevel rightCoefficients) else 0) := by
  classical
  have actualState (beta : Charge D) (level : ℤ)
      (coefficients : TransverseDownIndex D xAxis yAxis level →₀ ℂ) :
      ((energyTransverseDownCombination D H frame inverse leftGramInverse rightGramInverse
        leftFrameInverse rightFrameInverse xAxis yAxis beta level coefficients).val : State D) =
      Finsupp.single beta (transverseDownOscillator D frame xAxis yAxis level coefficients) ⊗ₜ[ℂ] down := by
    simp only [energyTransverseDownCombination, transverseDownOscillator,
      Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul,
      energyTransverseDownInput, nativeWord, downWord, Finset.sort_empty, List.map_nil,
      List.prod_nil, Module.End.one_apply, Finsupp.single_finsetSum, Finsupp.smul_single,
      TensorProduct.sum_tmul, TensorProduct.smul_tmul']
  rw [energyReducedInclusion_c0_pairing D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse nullDirection xAxis yAxis null distinct xRow xReal yReal
    xDual yDual leftCharge rightCharge leftLevel rightLevel leftNonzero rightNonzero leftYRow rightYRow]
  rw [actualState, actualState, F_c0_down_normalization,
    LatticeChargedFockForms.hermitian_single]

#print axioms energyReducedInclusion_c0_pairing
#print axioms energyTransverseDownInput
#print axioms energyTransverseDownCombination
#print axioms energyReducedInclusion_transverse_down_normalization

end
end D5.S3.VertexAlgebra.OriginalQEnergyInclusionPairing
