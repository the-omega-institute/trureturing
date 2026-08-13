/- GID: D5/S3/Zeros/MirrorPairIdentity
   generality: I
   mirror-B: D5/B/S3/Zeros/MirrorPairIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The mirror operation on a complex coordinate is involutive. -/

import Mathlib.Data.Complex.Basic

namespace D5.S3.Zeros.MirrorPairIdentity

open scoped ComplexConjugate

/-- Applying the reflected-conjugate coordinate map twice returns the input. -/
theorem mirror_pair_involution (rho : ℂ) :
    1 - conj (1 - conj rho) = rho := by
  simp

#print axioms mirror_pair_involution

end D5.S3.Zeros.MirrorPairIdentity
