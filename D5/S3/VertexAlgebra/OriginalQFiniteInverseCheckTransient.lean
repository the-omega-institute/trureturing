import D5.S3.VertexAlgebra.OriginalQFiniteInverseTransient
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

run_elab do
  Lean.Elab.Command.liftTermElabM do
    if let some output ← IO.getEnv "FRAME_ATTEMPT" then
      let names := #[``original_normalized_perturbation_termination,
        ``finiteOriginalCorrectionInverse, ``geom_sum_mul_neg, ``mul_neg_geom_sum]
      let mut fields := []
      for supplier in names do
        let declaration ← Lean.getConstInfo supplier
        let rendered ← Lean.Meta.ppExpr declaration.type
        fields := fields ++ [(supplier.toString, Lean.toJson rendered.pretty)]
      IO.FS.writeFile (System.FilePath.mk output / "inverse-supplier-types.json")
        (Lean.Json.mkObj fields).compress

include leftGramInverse rightGramInverse in
theorem original_finite_correction_inverse_on_energy
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (level : ℤ) (state : State D) (sector : chargeProjection D beta state = state)
    (energy : (M D H 0 + G D 0) state = (chosenH D beta + (level : ℂ) - 1) • state) :
    (finiteInverse level * (1 + correction)) state = state ∧
      ((1 + correction) * finiteInverse level) state = state := by
  run_tac do
    try
      Lean.Elab.Term.withoutErrToSorry <| Lean.Elab.Tactic.withoutRecover <|
        Lean.Elab.Tactic.evalTacticSeq (← `(tacticSeq|
        have termination := original_normalized_perturbation_termination D H frame inverse
          leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis
          null nonzero distinct xRow yRow xDual yDual level state sector energy
        let C : Module.End ℂ (State D) := correction
        have terminationC : (C ^ (2 * level.toNat + 2)) state = 0 := by
          exact termination
        have signedTermination : ((-correction : Module.End ℂ (State D)) ^
            (2 * level.toNat + 2)) state = 0 := by
          change ((-C) ^ (2 * level.toNat + 2)) state = 0
          have powerIdentity :
              ((-C) ^ (2 * level.toNat + 2)) =
                ((-1 : Module.End ℂ (State D)) ^ (2 * level.toNat + 2)) *
                  (C ^ (2 * level.toNat + 2)) := by
            exact neg_pow C (2 * level.toNat + 2)
          have zeroPower : (C ^ (2 * level.toNat + 2)) state = 0 := terminationC
          have applied := congrArg (fun operator : Module.End ℂ (State D) => operator state)
            powerIdentity
          calc
            ((-C) ^ (2 * level.toNat + 2)) state =
                (((-1 : Module.End ℂ (State D)) ^ (2 * level.toNat + 2)) *
                  (C ^ (2 * level.toNat + 2))) state := applied
            _ = ((-1 : Module.End ℂ (State D)) ^ (2 * level.toNat + 2))
                ((C ^ (2 * level.toNat + 2)) state) := by
              simp only [Module.End.mul_apply]
            _ = 0 := by
              have rightZero :
                  (((-1 : Module.End ℂ (State D)) ^ (2 * level.toNat + 2)) *
                    (C ^ (2 * level.toNat + 2))) state = 0 := by
                rw [Module.End.mul_apply, zeroPower]
                exact LinearMap.map_zero _
              exact rightZero
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
      ))
    catch exception =>
      if let some output ← IO.getEnv "FRAME_ATTEMPT" then
        let message ← exception.toMessageData.toString
        let diagnostic := Lean.Json.mkObj [("kind", Lean.toJson "own-proof-elaboration"),
          ("module", Lean.toJson "OriginalQFiniteInverseCheckTransient"),
          ("message", Lean.toJson message)]
        IO.FS.writeFile (System.FilePath.mk output / "inverse-elaboration-diagnostic.json")
          diagnostic.compress
      throw exception

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
