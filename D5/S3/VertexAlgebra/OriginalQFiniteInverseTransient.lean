import D5.S3.VertexAlgebra.LatticeBcGhostPerturbationTermination
import D5.S3.VertexAlgebra.TemporaryTransverseJointContraction19
import D5.S3.VertexAlgebra.LatticeBcGhostBrstNilpotence
import Mathlib.Algebra.Ring.GeomSum

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

def finiteOriginalCorrectionInverse (level : ℤ) : Module.End ℂ (State D) :=
  ∑ steps ∈ Finset.range (2 * level.toNat + 2), (-correction) ^ steps

local notation "finiteInverse" => finiteOriginalCorrectionInverse D H frame inverse
  leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis

def finiteOriginalTransferredDifferential (level : ℤ) : Module.End ℂ (State D) :=
  projector * (Q D H - leading) * finiteInverse level * projector

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
