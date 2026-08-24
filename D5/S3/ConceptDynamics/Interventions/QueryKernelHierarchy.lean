/- GID: D5/S3/ConceptDynamics/Interventions/QueryKernelHierarchy
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interventions/QueryKernelHierarchy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Query-law collapse maps force the observation, intervention, and counterfactual kernel chain. -/

import Mathlib.Data.Bool.Basic
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-25):
   * No existing D5 declaration packages a three-layer observation/intervention/
     counterfactual query-kernel chain; the nearest frozen declarations are
     special Boolean separation witnesses and are not general kernel inclusions.
   * Pinned Mathlib supplies `Setoid.ker`, function extensionality, and equality
     congruence; no query-family theorem was found. The generic proof below uses
     those primitives directly and constructs a concrete strictness witness.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Interventions.QueryKernelHierarchy

/- The query-law maps themselves are the source primitives; kernels are their
   equality relations, so no new quotient carrier is introduced. -/
theorem query_kernel_chain
    {Model Observation Intervention Counterfactual : Type*}
    (observationLaw : Model -> Observation)
    (interventionLaw : Model -> Intervention)
    (counterfactualLaw : Model -> Counterfactual)
    (observationFromIntervention : Intervention -> Observation)
    (interventionFromCounterfactual : Counterfactual -> Intervention)
    (observationCollapse : observationLaw =
      observationFromIntervention ∘ interventionLaw)
    (interventionCollapse : interventionLaw =
      interventionFromCounterfactual ∘ counterfactualLaw) :
    Setoid.ker counterfactualLaw ≤ Setoid.ker interventionLaw ∧
      Setoid.ker interventionLaw ≤ Setoid.ker observationLaw := by
  constructor
  · intro first second hEqual
    calc
      interventionLaw first =
          interventionFromCounterfactual (counterfactualLaw first) := by
        simpa only [Function.comp_apply] using congrFun interventionCollapse first
      _ = interventionFromCounterfactual (counterfactualLaw second) :=
        congrArg interventionFromCounterfactual hEqual
      _ = interventionLaw second := by
        simpa only [Function.comp_apply] using
          (congrFun interventionCollapse second).symm
  · intro first second hEqual
    calc
      observationLaw first =
          observationFromIntervention (interventionLaw first) := by
        simpa only [Function.comp_apply] using congrFun observationCollapse first
      _ = observationFromIntervention (interventionLaw second) :=
        congrArg observationFromIntervention hEqual
      _ = observationLaw second := by
        simpa only [Function.comp_apply] using
          (congrFun observationCollapse second).symm

abbrev LayeredState := Bool × (Bool × Bool)
abbrev LayeredIntervention := Bool × Bool

/-- A three-coordinate law retains successively more query information. -/
def layeredObservation : LayeredState -> Bool := fun state => state.1

def layeredIntervention : LayeredState -> LayeredIntervention :=
  fun state => (state.1, state.2.1)

def layeredCounterfactual : LayeredState -> LayeredState := id

def observationProjection : LayeredIntervention -> Bool := Prod.fst

def interventionProjection : LayeredState -> LayeredIntervention :=
  layeredIntervention

theorem layered_observation_collapse :
    layeredObservation = observationProjection ∘ layeredIntervention := by
  funext state
  rfl

theorem layered_intervention_collapse :
    layeredIntervention = interventionProjection ∘ layeredCounterfactual := by
  funext state
  rfl

/-- Both kernel inclusions can be strict in one concrete query system. -/
theorem observation_intervention_counterfactual_kernel_chain :
    (Setoid.ker layeredCounterfactual ≤ Setoid.ker layeredIntervention ∧
      Setoid.ker layeredIntervention ≤ Setoid.ker layeredObservation) ∧
    (∃ first second : LayeredState,
      layeredObservation first = layeredObservation second ∧
        layeredIntervention first ≠ layeredIntervention second) ∧
    (∃ first second : LayeredState,
      layeredIntervention first = layeredIntervention second ∧
        layeredCounterfactual first ≠ layeredCounterfactual second) := by
  have hChain := query_kernel_chain
    layeredObservation layeredIntervention layeredCounterfactual
    observationProjection interventionProjection
    layered_observation_collapse layered_intervention_collapse
  refine ⟨hChain, ?_, ?_⟩
  · refine ⟨(false, (false, false)), (false, (true, false)), ?_, ?_⟩
    · rfl
    · decide
  · refine ⟨(false, (false, false)), (false, (false, true)), ?_, ?_⟩
    · rfl
    · decide

#print axioms query_kernel_chain
#print axioms observation_intervention_counterfactual_kernel_chain

end D5.S3.ConceptDynamics.Interventions.QueryKernelHierarchy
