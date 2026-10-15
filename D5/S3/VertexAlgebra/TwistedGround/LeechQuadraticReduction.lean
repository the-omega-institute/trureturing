/- GID: D5/S3/VertexAlgebra/TwistedGround/LeechQuadraticReduction
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/LeechQuadraticReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original mod-two cocycle diagonal is the half-norm quadratic refinement. -/

import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
import Mathlib.LinearAlgebra.QuadraticForm.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open scoped BigOperators

noncomputable section

def quadratic (D : LatticeData) : QuadraticForm F₂ (ModTwoCharge D) :=
  (Matrix.toBilin' ((lowerMatrix D).map (Int.castRingHom F₂))).toQuadraticMap

theorem quadratic_diagonal (D : LatticeData) (charge : ModTwoCharge D) :
    quadratic D charge = modTwoCocycle D charge charge := rfl

theorem quadratic_integral (D : LatticeData) (charge : Charge D) :
    quadratic D (reduceCharge D charge) = (bilinear D charge charge / 2 : ℤ) := by
  rw [quadratic_diagonal, cocycle_reduction]
  change (lowerCocycleExponent D charge charge : F₂) = _
  rw [integral_cocycle_square]

end

end D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic
