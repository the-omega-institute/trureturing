/- GID: D5/S3/ConceptDynamics/MeasurableRefinement/MeasurableFactorInformationInclusion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/MeasurableRefinement/MeasurableFactorInformationInclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A measurable factorization includes the generated information space. -/

import D5.S3.ConceptDynamics.MeasurableRefinement.DoobDynkinFactorization

/- Library-search audit trail (2026-08-25):
   * Exact pinned-Mathlib hit
     `MeasurableSpace.comap_le_comap_of_eq_comp` states the unrestricted
     forward theorem on pullback measurable spaces and is applied directly.
   * The existing D5 Doob-Dynkin theorem packages a stronger equivalence under
     nonempty standard-Borel assumptions. It is not an exact bind-only hit for
     this unrestricted forward atom, but its canonical `Concept` carrier and
     generated-information representation are imported here.
   * Repository searches found no separate unrestricted D5 declaration with
     this exact signature. No definition or abbreviation is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.MeasurableRefinement.MeasurableFactorInformationInclusion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- If a concept readout is a measurable postprocessing of another readout,
then every event measurable from the first is measurable from the second. -/
theorem measurable_factorization_generated_information_inclusion
    {X B_C B_D : Type*} [MeasurableSpace B_C] [MeasurableSpace B_D]
    (C : Concept X B_C) (D : Concept X B_D) (p : B_D -> B_C)
    (hp : Measurable p) (factorization : C = p ∘ D) :
    MeasurableSpace.comap C inferInstance <=
      MeasurableSpace.comap D inferInstance :=
  MeasurableSpace.comap_le_comap_of_eq_comp p hp factorization

#print axioms measurable_factorization_generated_information_inclusion

end D5.S3.ConceptDynamics.MeasurableRefinement.MeasurableFactorInformationInclusion
