import D5.S3.VertexAlgebra.TemporaryNativeIndependent14

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
  LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

def transverseEpsilonSpace (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank) :
    Submodule ℂ (State D) :=
  Submodule.span ℂ {state | ∃ (charge : Charge D) (powers : Index D →₀ ℕ) (subset : Finset ℕ),
    (∀ frequency : ℕ, powers (xAxis, frequency) = 0) ∧
    (∀ frequency : ℕ, powers (yAxis, frequency) = 0) ∧ subset ⊆ {3} ∧
    state = nativeState D frame charge powers 1 subset}


end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
