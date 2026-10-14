import D5.S3.VertexAlgebra.OriginalQFiniteInverseTransient
import D5.S3.VertexAlgebra.TemporaryTransverseJointContraction19

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraVirasoro
  LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

variable (D : LatticeData)
variable (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
variable (beta : Charge D) (nullDirection : Fin D.rank → ℂ)
variable (xAxis yAxis : Fin D.rank)

local notation "normalized" => S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
  (chosenP D beta nullDirection)
local notation "leading" => delta D (adaptedPartner D beta nullDirection) (chosenP D beta nullDirection)
local notation "projector" => P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis

def finiteOriginalTransferredDifferential (level : ℤ) : Module.End ℂ (State D) :=
  projector * (Q D H - leading) *
    finiteOriginalCorrectionInverse D H frame inverse leftFrameInverse rightFrameInverse
      beta nullDirection xAxis yAxis level * projector

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
