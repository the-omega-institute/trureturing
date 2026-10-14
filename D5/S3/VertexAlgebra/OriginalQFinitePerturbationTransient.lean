import D5.S3.VertexAlgebra.OriginalQFiniteInverseCheckTransient
import D5.S3.VertexAlgebra.TemporaryTransverseJointContraction19
import D5.S3.VertexAlgebra.LatticeBcGhostBrstNilpotence
import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option hygiene false

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

theorem original_projector_preserves_charge
    (state : State D) (sector : chargeProjection D beta state = state) :
    chargeProjection D beta (projector state) = projector state := by
  run_tac do
    try
      Lean.Elab.Term.withoutErrToSorry <| Lean.Elab.Tactic.withoutRecover <|
        Lean.Elab.Tactic.evalTacticSeq (← `(tacticSeq|
        have diagonal (index : NativeIndex D) :
            projector (nativeWord D frame beta index) =
              (if kappa D xAxis yAxis index.1 index.2 = 0 then 1 else 0 : ℂ) •
                nativeWord D frame beta index :=
          P_native D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis beta index.1 1 index.2
        have expansion := native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse
          beta state sector
        calc
          _ = chargeProjection D beta (projector
              (∑ index ∈ (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta state).support,
                nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta state index •
                  nativeWord D frame beta index)) := by rw [expansion]
          _ = projector
              (∑ index ∈ (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta state).support,
                nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta state index •
                  nativeWord D frame beta index) := by
            simp only [map_sum, map_smul, diagonal, nativeWord_sector]
          _ = _ := by rw [expansion]
      ))
    catch exception =>
      if let some output ← IO.getEnv "FRAME_ATTEMPT" then
        let message ← exception.toMessageData.toString
        let diagnostic := Lean.Json.mkObj [("kind", Lean.toJson "own-proof-elaboration"),
          ("declaration", Lean.toJson "original_projector_preserves_charge"), ("message", Lean.toJson message)]
        IO.FS.writeFile (System.FilePath.mk output / "original_projector_preserves_charge.elaboration-diagnostic.json")
          diagnostic.compress
      throw exception

include leftGramInverse rightGramInverse in
theorem original_projector_preserves_energy
    (level : ℤ) (state : State D)
    (energy : (M D H 0 + G D 0) state = (chosenH D beta + (level : ℂ) - 1) • state) :
    (M D H 0 + G D 0) (projector state) =
      (chosenH D beta + (level : ℂ) - 1) • projector state := by
  run_tac do
    try
      Lean.Elab.Term.withoutErrToSorry <| Lean.Elab.Tactic.withoutRecover <|
        Lean.Elab.Tactic.evalTacticSeq (← `(tacticSeq|
        have commutation := (native_totalZero_Kdagger_P_commute D frame inverse
          leftFrameInverse rightFrameInverse xAxis yAxis H leftGramInverse rightGramInverse).2
        have equation := LinearMap.congr_fun commutation state
        change (M D H 0 + G D 0) (projector state) = projector ((M D H 0 + G D 0) state) at equation
        rw [equation, energy, map_smul]
      ))
    catch exception =>
      if let some output ← IO.getEnv "FRAME_ATTEMPT" then
        let message ← exception.toMessageData.toString
        let diagnostic := Lean.Json.mkObj [("kind", Lean.toJson "own-proof-elaboration"),
          ("declaration", Lean.toJson "original_projector_preserves_energy"), ("message", Lean.toJson message)]
        IO.FS.writeFile (System.FilePath.mk output / "original_projector_preserves_energy.elaboration-diagnostic.json")
          diagnostic.compress
      throw exception

include leftGramInverse rightGramInverse in
theorem original_Q_correction_intertwining
    (critical : D.rank = 26) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0) :
    (1 + correction) * Q D H = leading * (1 + correction) + projector * (Q D H - leading) := by
  run_tac do
    try
      Lean.Elab.Term.withoutErrToSorry <| Lean.Elab.Tactic.withoutRecover <|
        Lean.Elab.Tactic.evalTacticSeq (← `(tacticSeq|
        have contraction := original_chosen_normalized_strong_contraction D beta nullDirection
          frame inverse leftFrameInverse rightFrameInverse xAxis yAxis distinct xRow yRow xDual yDual nonzero
        have squares := original_delta_R_square_and_K_commute D frame xAxis yAxis distinct xDual yDual
          (chosenP D beta nullDirection) nonzero
        have leadingSquare : leading * leading = 0 := by
          simpa only [yRow] using squares.1
        have originalSquare := LatticeBcGhostBrstNilpotence.nilpotent D H
          leftGramInverse rightGramInverse critical
        apply sub_eq_zero.mp
        calc
          _ = normalized * (Q D H * Q D H) - normalized * (leading * leading) +
              (1 - projector - (leading * normalized + normalized * leading)) * (Q D H - leading) := by
            noncomm_ring
          _ = 0 := by rw [originalSquare, leadingSquare, contraction.1]; simp
      ))
    catch exception =>
      if let some output ← IO.getEnv "FRAME_ATTEMPT" then
        let message ← exception.toMessageData.toString
        let diagnostic := Lean.Json.mkObj [("kind", Lean.toJson "own-proof-elaboration"),
          ("declaration", Lean.toJson "original_Q_correction_intertwining"), ("message", Lean.toJson message)]
        IO.FS.writeFile (System.FilePath.mk output / "original_Q_correction_intertwining.elaboration-diagnostic.json")
          diagnostic.compress
      throw exception

include leftGramInverse rightGramInverse in
theorem original_finite_inclusion_defect
    (critical : D.rank = 26) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (level : ℤ) :
    Q D H * finiteInverse level * projector - finiteInverse level * projector *
        finiteOriginalTransferredDifferential D H frame inverse leftFrameInverse rightFrameInverse
          beta nullDirection xAxis yAxis level =
      (-correction) ^ (2 * level.toNat + 2) * Q D H * finiteInverse level * projector -
        finiteInverse level * leading * (-correction) ^ (2 * level.toNat + 2) * projector := by
  run_tac do
    try
      Lean.Elab.Term.withoutErrToSorry <| Lean.Elab.Tactic.withoutRecover <|
        Lean.Elab.Tactic.evalTacticSeq (← `(tacticSeq|
        let residual := (-correction) ^ (2 * level.toNat + 2)
        have rightGeometric : finiteInverse level * (1 + correction) = 1 - residual := by
          simpa only [sub_neg_eq_add, finiteOriginalCorrectionInverse] using
            geom_sum_mul_neg (-correction) (2 * level.toNat + 2)
        have leftGeometric : (1 + correction) * finiteInverse level = 1 - residual := by
          simpa only [sub_neg_eq_add, finiteOriginalCorrectionInverse] using
            mul_neg_geom_sum (-correction) (2 * level.toNat + 2)
        have intertwining := original_Q_correction_intertwining D H frame inverse leftGramInverse
          rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis
          critical nonzero distinct xRow yRow xDual yDual
        have contraction := original_chosen_normalized_strong_contraction D beta nullDirection
          frame inverse leftFrameInverse rightFrameInverse xAxis yAxis distinct xRow yRow xDual yDual nonzero
        have projectionSquare := native_P_idempotent D frame inverse leftFrameInverse rightFrameInverse
          xAxis yAxis
        have equation : (1 - residual) * Q D H * finiteInverse level * projector =
            finiteInverse level * leading * (1 - residual) * projector +
              finiteInverse level * projector * (Q D H - leading) * finiteInverse level * projector := by
          calc
            _ = finiteInverse level * ((1 + correction) * Q D H) * finiteInverse level * projector := by
              rw [← rightGeometric]
              noncomm_ring
            _ = _ := by
              rw [intertwining]
              calc
                _ = finiteInverse level * leading * ((1 + correction) * finiteInverse level) * projector +
                    finiteInverse level * projector * (Q D H - leading) * finiteInverse level * projector := by
                  noncomm_ring
                _ = _ := by rw [leftGeometric]
        have rearranged : Q D H * finiteInverse level * projector -
            finiteInverse level * projector * (Q D H - leading) * finiteInverse level * projector =
            residual * Q D H * finiteInverse level * projector +
              finiteInverse level * (leading * projector) - finiteInverse level * leading * residual * projector := by
          apply sub_eq_zero.mp
          calc
            _ = (1 - residual) * Q D H * finiteInverse level * projector -
                (finiteInverse level * leading * (1 - residual) * projector +
                  finiteInverse level * projector * (Q D H - leading) * finiteInverse level * projector) := by
              noncomm_ring
            _ = 0 := sub_eq_zero.mpr equation
        simp only [contraction.2.2.2.2.1, mul_zero, add_zero] at rearranged
        have nestedProjection : finiteInverse level * projector *
            finiteOriginalTransferredDifferential D H frame inverse leftFrameInverse rightFrameInverse
              beta nullDirection xAxis yAxis level =
            finiteInverse level * projector * (Q D H - leading) * finiteInverse level * projector := by
          dsimp only [finiteOriginalTransferredDifferential]
          calc
            _ = finiteInverse level * (projector * projector) * (Q D H - leading) *
                finiteInverse level * projector := by noncomm_ring
            _ = _ := by rw [projectionSquare]
        rw [nestedProjection]
        exact rearranged
      ))
    catch exception =>
      if let some output ← IO.getEnv "FRAME_ATTEMPT" then
        let message ← exception.toMessageData.toString
        let diagnostic := Lean.Json.mkObj [("kind", Lean.toJson "own-proof-elaboration"),
          ("declaration", Lean.toJson "original_finite_inclusion_defect"), ("message", Lean.toJson message)]
        IO.FS.writeFile (System.FilePath.mk output / "original_finite_inclusion_defect.elaboration-diagnostic.json")
          diagnostic.compress
      throw exception

include leftGramInverse rightGramInverse in
theorem original_finite_corrected_Q_equation_on_energy
    (critical : D.rank = 26)
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (level : ℤ) (state : State D) (sector : chargeProjection D beta state = state)
    (energy : (M D H 0 + G D 0) state = (chosenH D beta + (level : ℂ) - 1) • state) :
    ((1 + correction) * Q D H * finiteInverse level * projector) state =
      finiteOriginalTransferredDifferential D H frame inverse leftFrameInverse rightFrameInverse
        beta nullDirection xAxis yAxis level state := by
  run_tac do
    try
      Lean.Elab.Term.withoutErrToSorry <| Lean.Elab.Tactic.withoutRecover <|
        Lean.Elab.Tactic.evalTacticSeq (← `(tacticSeq|
        have projectedSector := original_projector_preserves_charge D frame inverse leftFrameInverse
          rightFrameInverse beta xAxis yAxis state sector
        have projectedEnergy := original_projector_preserves_energy D H frame inverse leftGramInverse
          rightGramInverse leftFrameInverse rightFrameInverse beta xAxis yAxis level state energy
        have inverseEquation := (original_finite_correction_inverse_on_energy D H frame inverse
          leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis
          null nonzero distinct xRow yRow xDual yDual level (projector state) projectedSector projectedEnergy).2
        have intertwining := original_Q_correction_intertwining D H frame inverse leftGramInverse
          rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis
          critical nonzero distinct xRow yRow xDual yDual
        have contraction := original_chosen_normalized_strong_contraction D beta nullDirection
          frame inverse leftFrameInverse rightFrameInverse xAxis yAxis distinct xRow yRow xDual yDual nonzero
        have operatorEquation :
            (1 + correction) * Q D H * finiteInverse level * projector =
            leading * ((1 + correction) * finiteInverse level) * projector +
              finiteOriginalTransferredDifferential D H frame inverse leftFrameInverse rightFrameInverse
                beta nullDirection xAxis yAxis level := by
          rw [intertwining]
          dsimp only [finiteOriginalTransferredDifferential]
          noncomm_ring
        have equation := LinearMap.congr_fun operatorEquation state
        simp only [LinearMap.add_apply, Module.End.mul_apply] at equation inverseEquation
        rw [inverseEquation] at equation
        have vanishing := LinearMap.congr_fun contraction.2.2.2.2.1 state
        simp only [Module.End.mul_apply, LinearMap.zero_apply] at vanishing
        simpa only [vanishing, zero_add, Module.End.mul_apply] using equation
      ))
    catch exception =>
      if let some output ← IO.getEnv "FRAME_ATTEMPT" then
        let message ← exception.toMessageData.toString
        let diagnostic := Lean.Json.mkObj [("kind", Lean.toJson "own-proof-elaboration"),
          ("declaration", Lean.toJson "original_finite_corrected_Q_equation_on_energy"), ("message", Lean.toJson message)]
        IO.FS.writeFile (System.FilePath.mk output / "original_finite_corrected_Q_equation_on_energy.elaboration-diagnostic.json")
          diagnostic.compress
      throw exception

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
