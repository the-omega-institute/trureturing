/- GID: D5/S3/ConceptDynamics/Gluing/LocalFactorOverlapCompatibility
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Gluing/LocalFactorOverlapCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Local factors of a surjective readout agree on every overlap. -/

import Mathlib.Data.Set.Basic

/- Library-search audit trail (2026-08-25):
   * Repository searches for surjective readouts, local factors on subtype
     domains, and equality on overlaps found adjacent descent and gluing modules
     but no theorem with this source carrier and conclusion.
   * Body-shape searches for `Function.Surjective q`, `q x ∈ U i`, dependent
     local maps, and `f i b = f j b` found no canonical D5 primitive to import.
   * Pinned Mathlib supplies `Function.Surjective` and subtype proof
     irrelevance, but no packaged local-factor compatibility theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Gluing.LocalFactorOverlapCompatibility

/-- Local interpretations defined on the exact cover subtypes agree on every
overlap whenever they all factor one target through a surjective readout. The
openness, cover-totality, and continuity assumptions of a later gluing step are
not needed for this compatibility consequence. -/
theorem local_factor_overlap_compatibility
    {Index X B Y : Type*} (q : X -> B) (target : X -> Y)
    (domain : Index -> Set B)
    (localFactor : (i : Index) -> {b : B // b ∈ domain i} -> Y)
    (surjective : Function.Surjective q)
    (factors : ∀ i x (membership : q x ∈ domain i),
      target x = localFactor i ⟨q x, membership⟩) :
    ∀ i j b (inFirst : b ∈ domain i) (inSecond : b ∈ domain j),
      localFactor i ⟨b, inFirst⟩ = localFactor j ⟨b, inSecond⟩ := by
  intro i j b inFirst inSecond
  obtain ⟨x, rfl⟩ := surjective b
  calc
    localFactor i ⟨q x, inFirst⟩ = target x := (factors i x inFirst).symm
    _ = localFactor j ⟨q x, inSecond⟩ := factors j x inSecond

#print axioms local_factor_overlap_compatibility

end D5.S3.ConceptDynamics.Gluing.LocalFactorOverlapCompatibility
