/- GID: D5/S3/VertexAlgebra/TwistedGround/LeechHyperbolicCertificate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/LeechHyperbolicCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The literal Leech frame has twenty-four singular vectors and hyperbolic pairings. -/

import D5.S3.VertexAlgebra.TwistedGround.LeechQuadraticReduction
import D5.S3.VertexAlgebra.TwistedGround.LeechFrameRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open GolayLeech.ExplicitLeechLattice GolayLeech.ExplicitLeechBasis
open scoped BigOperators

noncomputable section

def frameIndex : Fin 12 ⊕ Fin 12 → Fin 24
  | Sum.inl index => Fin.castAdd 12 index
  | Sum.inr index => Fin.natAdd 12 index

def integralFrame (index : Fin 12 ⊕ Fin 12) : Charge data :=
  literalIntegralVectors (frameIndex index)

def frame (index : Fin 12 ⊕ Fin 12) : ModTwoCharge data :=
  reduceCharge data (integralFrame index)

def partner : Fin 12 ⊕ Fin 12 → Fin 12 ⊕ Fin 12
  | Sum.inl index => Sum.inr index
  | Sum.inr index => Sum.inl index

theorem literal_certificate :
    (∀ index, quadratic data (frame index) = 0) ∧
    (∀ first second, modTwoPairing data (frame first) (frame second) =
      if partner first = second then 1 else 0) := by
  have norms : ∀ index : Fin 12 ⊕ Fin 12,
      ((bilinear data (integralFrame index) (integralFrame index) / 2 : ℤ) : F₂) = 0 := by
    simp only [integralFrame, literal_gram_entry]
    rintro (index | index) <;> fin_cases index <;> decide +kernel
  have pairings : ∀ first second : Fin 12 ⊕ Fin 12,
      (bilinear data (integralFrame first) (integralFrame second) : F₂) =
        if partner first = second then 1 else 0 := by
    simp only [integralFrame, literal_gram_entry]
    rintro (first | first) (second | second) <;> fin_cases first <;> fin_cases second <;>
      decide +kernel
  constructor
  · intro index
    exact (quadratic_integral data (integralFrame index)).trans (norms index)
  · intro first second
    have reduction : modTwoPairing data (frame first) (frame second) =
        (bilinear data (integralFrame first) (integralFrame second) : F₂) := by
      simp [frame, modTwoPairing, Matrix.toBilin'_apply, Matrix.map_apply,
        reduceCharge, bilinear]
    exact reduction.trans (pairings first second)

end

end D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic
