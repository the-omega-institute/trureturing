/- GID: D5/S3/Quantum/Analysis/VonNeumannNormalL1
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/VonNeumannNormalL1
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The inherited C-star order on a concrete von Neumann algebra. -/

import D5.S3.Quantum.Analysis.NormalL1Realization
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

/-! # Concrete von Neumann algebras as targets of normal L1 realization

The carrier is the actual closed star subalgebra of bounded operators. Its
order is the inherited operator order. Order-normality refers to directed
suprema in this algebra; no identification with an abstract chosen predual
or an ultraweak topology is asserted.
-/

noncomputable section

namespace D5.S3.Quantum.Analysis.VonNeumannNormalL1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance closedCarrier (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  rw [VonNeumannAlgebra.coe_toStarSubalgebra, ← M.centralizer_centralizer]
  exact Set.isClosed_centralizer _

end D5.S3.Quantum.Analysis.VonNeumannNormalL1
