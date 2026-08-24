/- GID: D5/S3/ConceptDynamics/QueryLaws/QueryKernelHierarchyComplete
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/QueryLaws/QueryKernelHierarchyComplete
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Generic query-law kernel inclusion and concrete strictness are exposed together. -/

import D5.S3.ConceptDynamics.Interventions.QueryKernelHierarchy

/- Library-search audit trail (2026-08-25):
   * The canonical query-law primitives and concrete witnesses are imported from
     `QueryKernelHierarchy`; this split module only exposes the source theorem's
     generic chain and strictness clauses in one public declaration.
   * No pinned-Mathlib theorem packages this combined statement; the imported
     generic chain uses equality congruence and `Setoid.ker` directly.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.QueryLaws.QueryKernelHierarchyComplete

open D5.S3.ConceptDynamics.Interventions.QueryKernelHierarchy

theorem query_kernel_hierarchy_complete :
    (∀ {Model Observation Intervention Counterfactual : Type*}
      (observationLaw : Model -> Observation)
      (interventionLaw : Model -> Intervention)
      (counterfactualLaw : Model -> Counterfactual)
      (observationFromIntervention : Intervention -> Observation)
      (interventionFromCounterfactual : Counterfactual -> Intervention),
      observationLaw = observationFromIntervention ∘ interventionLaw ->
        interventionLaw = interventionFromCounterfactual ∘ counterfactualLaw ->
          Setoid.ker counterfactualLaw <= Setoid.ker interventionLaw ∧
            Setoid.ker interventionLaw <= Setoid.ker observationLaw) ∧
    (∃ first second : LayeredState,
      layeredObservation first = layeredObservation second ∧
        layeredIntervention first ≠ layeredIntervention second) ∧
    (∃ first second : LayeredState,
      layeredIntervention first = layeredIntervention second ∧
        layeredCounterfactual first ≠ layeredCounterfactual second) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Model Observation Intervention Counterfactual
      observationLaw interventionLaw counterfactualLaw
      observationFromIntervention interventionFromCounterfactual
      observationCollapse interventionCollapse
    exact query_kernel_chain observationLaw interventionLaw counterfactualLaw
      observationFromIntervention interventionFromCounterfactual
      observationCollapse interventionCollapse
  · exact observation_intervention_counterfactual_kernel_chain.2.1
  · exact observation_intervention_counterfactual_kernel_chain.2.2

#print axioms query_kernel_hierarchy_complete

end D5.S3.ConceptDynamics.QueryLaws.QueryKernelHierarchyComplete
