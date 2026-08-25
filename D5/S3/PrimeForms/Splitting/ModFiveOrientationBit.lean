/- GID: D5/S3/PrimeForms/Splitting/ModFiveOrientationBit
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Splitting/ModFiveOrientationBit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The mod-five bit separates binary profile fibers but is not multiplicative. -/

import D5.S3.PrimeForms.Splitting.ThreeRingProfileFibers

/- Library-search audit trail (2026-08-25):
   * Repository searches for a modulo-five orientation bit on `(ZMod 60)ˣ`,
     maps from `(ZMod 60)ˣ` to `ZMod 2`, and the residue-test body below
     found no existing declaration.
   * The exact repository theorem
     `tri_ring_image_surjective_with_fibers_of_card_two` supplies the public
     two-element-fiber clause and is applied directly.
   * Pinned Mathlib supplies the finite unit group, `ZMod`, and its decidable
     arithmetic, but searches found no declaration packaging this orientation
     test, fiberwise separation, and non-homomorphism contrast. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.Splitting.ModFiveOrientationBit

open D5.S3.PrimeForms.Splitting.ThreeRingProfileFibers

/-- The source's orientation of the four unit residues modulo five. -/
def modFiveOrientation (u : (ZMod 60)ˣ) : ZMod 2 :=
  if u.val.val % 5 = 1 ∨ u.val.val % 5 = 2 then 0 else 1

/-- Every three-ring profile fiber has two elements and the modulo-five bit
separates its two unit classes, but the bit does not turn multiplication of
unit classes into addition in the binary cyclic group. -/
theorem mod_five_orientation_separates_fibers_but_is_not_homomorphic :
    ((∀ t, Fintype.card {u : (ZMod 60)ˣ // triRingImage u = t} = 2) ∧
      ∀ t u v, triRingImage u = t → triRingImage v = t →
        modFiveOrientation u = modFiveOrientation v → u = v) ∧
      ¬∀ u v, modFiveOrientation (u * v) =
        modFiveOrientation u + modFiveOrientation v := by
  refine ⟨⟨tri_ring_image_surjective_with_fibers_of_card_two.2, ?_⟩, ?_⟩
  · set_option maxRecDepth 100000 in
      decide
  · set_option maxRecDepth 100000 in
      decide

#print axioms mod_five_orientation_separates_fibers_but_is_not_homomorphic

end D5.S3.PrimeForms.Splitting.ModFiveOrientationBit
