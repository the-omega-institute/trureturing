import D5.S3.VertexAlgebra.OriginalQFiniteInverseTransient
import Mathlib.Algebra.Ring.Parity

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraVirasoro
  LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

variable (D : LatticeData)
variable (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
variable (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
variable (beta : Charge D) (nullDirection : Fin D.rank → ℂ)
variable (xAxis yAxis : Fin D.rank)

local notation "normalized" => S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
  (chosenP D beta nullDirection)
local notation "leading" => delta D (adaptedPartner D beta nullDirection) (chosenP D beta nullDirection)
local notation "projector" => P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
local notation "correction" => normalized * (Q D H - leading)
local notation "finiteInverse" => finiteOriginalCorrectionInverse D H frame inverse
  leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis

include leftGramInverse rightGramInverse in
theorem original_finite_inverse_actions
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (level : ℤ) (state : State D) (sector : chargeProjection D beta state = state)
    (energy : (M D H 0 + G D 0) state = (chosenH D beta + (level : ℂ) - 1) • state) :
    (finiteInverse level * (1 + correction)) state = state ∧
      ((1 + correction) * finiteInverse level) state = state := by
  have termination := original_normalized_perturbation_termination D H frame inverse
    leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis
    null nonzero distinct xRow yRow xDual yDual level state sector energy
  have evenCutoff : Even (2 * level.toNat + 2) := ⟨level.toNat + 1, by omega⟩
  have signedTermination : ((-correction : Module.End ℂ (State D)) ^
      (2 * level.toNat + 2)) state = 0 := by
    rw [evenCutoff.neg_pow (correction : Module.End ℂ (State D))]
    exact termination
  have rightGeometric : finiteInverse level * (1 + correction) =
      1 - (-correction) ^ (2 * level.toNat + 2) := by
    simpa only [sub_neg_eq_add, finiteOriginalCorrectionInverse] using
      geom_sum_mul_neg (-correction) (2 * level.toNat + 2)
  have leftGeometric : (1 + correction) * finiteInverse level =
      1 - (-correction) ^ (2 * level.toNat + 2) := by
    simpa only [sub_neg_eq_add, finiteOriginalCorrectionInverse] using
      mul_neg_geom_sum (-correction) (2 * level.toNat + 2)
  constructor
  · rw [rightGeometric]
    simp only [LinearMap.sub_apply, Module.End.one_apply, signedTermination, sub_zero]
  · rw [leftGeometric]
    simp only [LinearMap.sub_apply, Module.End.one_apply, signedTermination, sub_zero]

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
