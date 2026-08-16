/- GID: D5/S3/Arith/Congruence/CyclicTorsionFreeHomRigidity
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/CyclicTorsionFreeHomRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite cyclic group has no nonzero additive map to a torsion-free group. -/

import Mathlib.Algebra.Group.Torsion
import Mathlib.Data.ZMod.Basic

namespace D5.S3.Arith.Congruence.CyclicTorsionFreeHomRigidity

/-- Every additive homomorphism from a nontrivial finite cyclic group to a torsion-free additive
commutative monoid is zero. In particular, this applies to homomorphisms from `ZMod 12` to the
additive real numbers. -/
theorem zmod_hom_to_torsion_free_eq_zero {n : ℕ} (hn : n ≠ 0) {A : Type*}
    [AddCommMonoid A] [IsAddTorsionFree A] (f : ZMod n →+ A) :
    f = 0 := by
  ext x
  change f x = 0
  apply nsmul_right_injective hn
  change n • f x = n • (0 : A)
  simpa only [map_nsmul, map_zero, nsmul_zero] using
    congrArg f (ZModModule.char_nsmul_eq_zero n x)

#print axioms zmod_hom_to_torsion_free_eq_zero

end D5.S3.Arith.Congruence.CyclicTorsionFreeHomRigidity
