/- GID: D5/S3/VertexAlgebra/RelativePairing/RotatedAntighostAdjoint
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none -/

import D5.S3.VertexAlgebra.BcGhostRotatedForm

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostRotatedForm

open BcGhostFockSupport BcGhostEnergyRotation BcGhostBpZForm

noncomputable section

theorem Gplus_b (mode : ℤ) (left right : GhostFock) :
    Gplus (b mode left) right = Gplus (Pi left) (b (-mode) right) := by
  unfold Gplus
  rw [BPZ_b]
  have pass := congrArg (fun operator : Module.End ℂ GhostFock => operator right)
    (rotation_b (-mode))
  change rotation (b (-mode) right) = (-1 : ℂ) ^ (-mode) • b (-mode) (rotation right) at pass
  rw [pass, BPZ_linear_right, phase_neg]

theorem Hplus_b (mode : ℤ) (left right : GhostFock) :
    Hplus (b mode left) right = Hplus (Pi left) (b (-mode) right) := by
  change Gplus (conjCoeffs (b mode left)) right =
    Gplus (conjCoeffs (Pi left)) (b (-mode) right)
  rw [conjugation_b, conjugation_Pi, Gplus_b]

#print axioms Hplus_b

end

end D5.S3.VertexAlgebra.BcGhostRotatedForm
