/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeSameParityEvenExclusion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeSameParityEvenExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual Leech even twisted module has no nonzero integral same-parity field with odd source. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParityCurrentTopDetection
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParityEvenCurrent

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParity

open ActualLeechHyperbolic (leechData leech_spec)
open NativeOddTwistedIntertwiner (leechUnit)

/-- Every integral lawful field with actual Leech odd source and even
twisted input and output has zero coefficients at every integer label. -/
theorem leech_even_sameParity_coeff_eq_zero (F : LawfulField leechData leechUnit false) :
    F.coeff = 0 := by
  apply coeff_eq_zero_of_current_zero (by rw [leech_spec.1]; decide) leech_spec.2.2.1 F
  intro i v
  exact leech_even_sameParity_current_zero i F v

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParity
