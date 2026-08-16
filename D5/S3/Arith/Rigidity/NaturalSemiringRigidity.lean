/- GID: D5/S3/Arith/Rigidity/NaturalSemiringRigidity
   generality: G
   mirror-B: D5/B/S3/Arith/Rigidity/NaturalSemiringRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every semiring automorphism of the naturals is the identity. -/

import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Nat.Cast.Basic

namespace D5.S3.Arith.Rigidity.NaturalSemiringRigidity

/-- Every semiring automorphism of the natural numbers is the identity. -/
theorem natural_semiring_automorphism_is_identity (e : ℕ ≃+* ℕ) :
    e = RingEquiv.refl ℕ := by
  apply RingEquiv.ext
  intro n
  exact map_natCast e n

end D5.S3.Arith.Rigidity.NaturalSemiringRigidity
