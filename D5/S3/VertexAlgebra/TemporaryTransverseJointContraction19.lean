import D5.S3.VertexAlgebra.TemporaryTransverseJointContraction18
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic

set_option autoImplicit false

open scoped Classical

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

theorem original_chosen_normalized_strong_contraction (D : LatticeData)
    (charge : Charge D) (nullDirection : Fin D.rank → ℂ)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xRow : frame xAxis = nullDirection) (yRow : frame yAxis = adaptedPartner D charge nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (nonzero : chosenP D charge nullDirection ≠ 0) :
    let leading := delta D (adaptedPartner D charge nullDirection) (chosenP D charge nullDirection)
    let normalized := S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
      (chosenP D charge nullDirection)
    let projector := P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
    let nullHomotopy := R D nullDirection (chosenP D charge nullDirection)
    leading * normalized + normalized * leading = 1 - projector ∧
      normalized * normalized = 0 ∧ normalized * projector = 0 ∧ projector * normalized = 0 ∧
      leading * projector = 0 ∧ projector * leading = 0 ∧
      nullHomotopy * projector = 0 ∧ projector * nullHomotopy = 0 := by
  dsimp only
  simpa only [xRow, yRow] using
    original_normalized_strong_contraction D frame inverse leftFrameInverse rightFrameInverse
      xAxis yAxis distinct xDual yDual (chosenP D charge nullDirection) nonzero

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
