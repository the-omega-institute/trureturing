/- GID: D5/S3/ConceptDynamics/Negation/DirectImageComplementSaturation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Negation/DirectImageComplementSaturation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Surjective images preserve complements exactly on unions of whole fibers. -/

import Mathlib.Data.Set.Lattice

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Negation.DirectImageComplementSaturation

universe u v

/-- For a surjective readout, the image of a complement is the complement of
the image exactly when the selected set is a union of complete readout fibers. -/
theorem image_complement_iff_saturated
    {X : Type u} {B : Type v} (f : X → B)
    (hf : Function.Surjective f) (A : Set X) :
    f '' Aᶜ = (f '' A)ᶜ ↔ A = f ⁻¹' (f '' A) := by
  constructor
  · intro imageEquality
    apply Set.Subset.antisymm (Set.subset_preimage_image _ _)
    intro x xInSaturation
    by_contra xNotInA
    have imageOfComplement : f x ∈ f '' Aᶜ := ⟨x, xNotInA, rfl⟩
    rw [imageEquality] at imageOfComplement
    exact imageOfComplement xInSaturation
  · intro saturation
    calc
      f '' Aᶜ = f '' (f ⁻¹' (f '' A))ᶜ :=
        congrArg (fun selected : Set X => f '' selectedᶜ) saturation
      _ = Set.range f \ f '' A := Set.image_compl_preimage
      _ = (f '' A)ᶜ := by
        simp only [Set.range_eq_univ.mpr hf, Set.compl_eq_univ_sdiff]

#print axioms image_complement_iff_saturated

end D5.S3.ConceptDynamics.Negation.DirectImageComplementSaturation
