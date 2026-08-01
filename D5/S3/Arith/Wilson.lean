/- GID: D5/S3/Arith/Wilson
   generality: G
   mirror-B: D5/B/S3/Arith/Wilson
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Wilson's theorem identifies the factorial of one less than a prime modulo that prime. -/

import Mathlib.NumberTheory.Wilson

namespace D5.S3.Arith.Wilson

/-- Wilson's theorem in the residue ring modulo `p`. -/
theorem wilson_theorem (p : ℕ) (hp : Nat.Prime p) :
    (Nat.factorial (p - 1) : ZMod p) = -1 := by
  haveI := Fact.mk hp
  exact ZMod.wilsons_lemma p

end D5.S3.Arith.Wilson
