import D5.S3.VertexAlgebra.OriginalQFiniteTransferTransient

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQFiniteHplCheck

theorem correction_ring_intertwiners {Algebra : Type*} [Ring Algebra]
    (leading homotopy projector original : Algebra)
    (originalSquare : original * original = 0) (leadingSquare : leading * leading = 0)
    (contraction : leading * homotopy + homotopy * leading = 1 - projector) :
    (1 + homotopy * (original - leading)) * original =
      leading * (1 + homotopy * (original - leading)) + projector * (original - leading) ∧
    original * (1 + (original - leading) * homotopy) =
      (1 + (original - leading) * homotopy) * leading + (original - leading) * projector := by
  have pIdentity : projector = 1 - (leading * homotopy + homotopy * leading) := by
    rw [contraction]
    abel
  have leftCompatibility : leading * (original - leading) + (original - leading) * original = 0 := by
    calc
      _ = original * original - leading * leading := by noncomm_ring
      _ = 0 := by rw [originalSquare, leadingSquare, sub_self]
  have rightCompatibility : original * (original - leading) + (original - leading) * leading = 0 := by
    calc
      _ = original * original - leading * leading := by noncomm_ring
      _ = 0 := by rw [originalSquare, leadingSquare, sub_self]
  constructor
  · calc
      _ = leading * (1 + homotopy * (original - leading)) + projector * (original - leading) +
          homotopy * (leading * (original - leading) + (original - leading) * original) := by
            rw [pIdentity]
            noncomm_ring
      _ = _ := by rw [leftCompatibility, mul_zero, add_zero]
  · calc
      _ = (1 + (original - leading) * homotopy) * leading + (original - leading) * projector +
          (original * (original - leading) + (original - leading) * leading) * homotopy := by
            rw [pIdentity]
            noncomm_ring
      _ = _ := by rw [rightCompatibility, zero_mul, add_zero]

end D5.S3.VertexAlgebra.OriginalQFiniteHplCheck

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
local notation "perturbation" => Q D H - leading

include leftGramInverse rightGramInverse in
theorem original_correction_intertwiners
    (critical : D.rank = 26) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0) :
    Q D H * Q D H = 0 ∧ leading * leading = 0 ∧
      (1 + normalized * perturbation) * Q D H =
        leading * (1 + normalized * perturbation) + projector * perturbation ∧
      Q D H * (1 + perturbation * normalized) =
        (1 + perturbation * normalized) * leading + perturbation * projector := by
  have qSquare := LatticeBcGhostBrstNilpotence.nilpotent D H
    leftGramInverse rightGramInverse critical
  have dSquare : leading * leading = 0 := by
    have squares := original_delta_R_square_and_K_commute D frame xAxis yAxis
      distinct xDual yDual (chosenP D beta nullDirection) nonzero
    simpa only [yRow] using squares.1
  have strong := original_chosen_normalized_strong_contraction D beta nullDirection
    frame inverse leftFrameInverse rightFrameInverse xAxis yAxis distinct xRow yRow
    xDual yDual nonzero
  exact ⟨qSquare, dSquare, OriginalQFiniteHplCheck.correction_ring_intertwiners
    leading normalized projector (Q D H) qSquare dSquare strong.1⟩

run_elab do
  let environment ← Lean.getEnv
  for (name, declaration) in environment.constants.toList do
    if name.toString.startsWith
        "_private.D5.S3.VertexAlgebra.LatticeBcGhostPerturbationTermination." &&
        #["Q_sector", "dSum_sector", "normalized_sector", "totalZero_Q_commutes",
          "totalZero_dSum_commutes"].any (fun suffix => name.toString.endsWith suffix) then
      let rendered ← Lean.Meta.ppExpr declaration.type
      Lean.logInfo m!"{name}: {rendered}"

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
