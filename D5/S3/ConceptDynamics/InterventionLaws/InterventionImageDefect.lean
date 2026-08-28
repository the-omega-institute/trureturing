/- GID: D5/S3/ConceptDynamics/InterventionLaws/InterventionImageDefect
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InterventionLaws/InterventionImageDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A law family outside the intervention image has no joint explaining model. -/

import Mathlib.Data.Set.Function

/- Library-search audit trail (2026-08-26):
   * D5 name and body-shape searches found no declaration connecting
     nonmembership in an intervention-law image to simultaneous explanation of
     every regime.
   * The nearby frozen intervention-law modules construct particular Boolean
     structural models, but none states this image-level criterion.
   * Pinned Mathlib supplies `Set.mem_range`, whose statement is definitionally
     the existential range membership test, but no exact theorem on a restricted
     model class and its pointwise intervention profiles. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InterventionLaws.InterventionImageDefect

/-- If an observed law family lies outside the image of the intervention-law
map restricted to a model class, no member of that class explains every
intervention regime. -/
theorem image_defect_excludes_joint_model
    {Model Regime Law : Type*}
    (modelClass : Set Model)
    (interventionLaw : Model -> Regime -> Law)
    (observedLaw : Regime -> Law)
    (imageDefect :
      observedLaw ∉ Set.range
        (fun model : modelClass =>
          fun regime => interventionLaw model.1 regime)) :
    ¬ ∃ model : Model, model ∈ modelClass ∧
      ∀ regime, interventionLaw model regime = observedLaw regime := by
  rintro ⟨model, model_mem, explains_all⟩
  apply imageDefect
  exact ⟨⟨model, model_mem⟩, funext explains_all⟩

-- A nonempty model class can satisfy the image-defect hypothesis.
example :
    (fun _ : Unit => true) ∉ Set.range
      (fun _ : (Set.univ : Set Unit) => fun _ : Unit => false) := by
  rintro ⟨_, profile_eq⟩
  have : false = true := congrFun profile_eq ()
  contradiction

-- Without image defect, simultaneous explanation is possible.
example :
    ∃ model : Unit, model ∈ (Set.univ : Set Unit) ∧
      ∀ regime : Unit,
        (fun _ _ : Unit => false) model regime =
          (fun _ : Unit => false) regime := by
  exact ⟨(), Set.mem_univ (), fun _ => rfl⟩

#print axioms image_defect_excludes_joint_model

end D5.S3.ConceptDynamics.InterventionLaws.InterventionImageDefect
