/- GID: D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three profiles yield the kernel chain; strict and degenerate cases are explicit. -/
/- Library-search audit trail (2026-08-25):
   * Exact repository searches for the four profile names and premise-necessity theorems
     returned no match. `FiniteCausalQueryHierarchy` supplies both strict witness pairs.
   * `QueryKernelHierarchy` proves a related readback theorem, but does not encode the empty
     intervention, single-world membership premises, or their necessity counterexamples.
   * Pinned Mathlib supplies `Setoid.ker` and `Setoid.ker_def`; both kernel links below use
     that canonical equivalence relation rather than defining another function kernel.
   * Searches for `MeasureTheory.Kernel`, `PMF`, and `Function.Injective` found their standard
     APIs. They are unnecessary because the imported finite SCM already exposes exact laws.
 -/

import D5.S3.ConceptDynamics.Causal.FiniteCausalQueryHierarchy
import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.ThreeLayerCausalObservationLanguage

open D5.S3.ConceptDynamics.Causal.FiniteCausalQueryHierarchy

universe uModel uAction uQuery uLaw

/-- Definition 252.1: the passive joint law of the visible variables. -/
def observationalProfile {Model : Type uModel} {Law : Type uLaw}
    (observationLaw : Model -> Law) : Model -> Law :=
  observationLaw

/-- Definition 252.2: the family of visible-variable laws for the allowed interventions. -/
def interventionalProfile {Model : Type uModel} {Action : Type uAction}
    {Law : Type uLaw} (allowed : Set Action)
    (interventionLaw : Model -> Action -> Law) : Model -> allowed -> Law :=
  fun model action => interventionLaw model action.1

/-- Definition 252.3: the family of laws for the selected counterfactual queries. -/
def counterfactualProfile {Model : Type uModel} {Query : Type uQuery}
    {Law : Type uLaw} (queries : Set Query)
    (counterfactualLaw : Model -> Query -> Law) : Model -> queries -> Law :=
  fun model query => counterfactualLaw model query.1

/-- Definition 252.4: equality of each named profile induces its model setoid. -/
def threeLayerEquivalence {Model : Type uModel} {Action : Type uAction}
    {Query : Type uQuery} {Law : Type uLaw}
    (allowed : Set Action) (queries : Set Query)
    (observationLaw : Model -> Law) (interventionLaw : Model -> Action -> Law)
    (counterfactualLaw : Model -> Query -> Law) :
    Setoid Model × Setoid Model × Setoid Model :=
  (Setoid.ker (observationalProfile observationLaw),
    Setoid.ker (interventionalProfile allowed interventionLaw),
    Setoid.ker (counterfactualProfile queries counterfactualLaw))

/-- Principle 252.1: selected counterfactual equality implies selected intervention
equality, and the empty-intervention component then implies observational equality. -/
theorem causal_hierarchy_direction
    {Model : Type uModel} {Action : Type uAction} {Query : Type uQuery}
    {Law : Type uLaw} (allowed : Set Action) (queries : Set Query)
    (empty : Action) (singleWorld : Action -> Query)
    (observationLaw : Model -> Law) (interventionLaw : Model -> Action -> Law)
    (counterfactualLaw : Model -> Query -> Law)
    (emptyLaw : forall model, interventionLaw model empty = observationLaw model)
    (singleWorldLaw : forall model action,
      counterfactualLaw model (singleWorld action) = interventionLaw model action)
    (emptyAllowed : empty ∈ allowed)
    (singleWorldQueried : forall action, action ∈ allowed -> singleWorld action ∈ queries) :
    Setoid.ker (counterfactualProfile queries counterfactualLaw) <=
        Setoid.ker (interventionalProfile allowed interventionLaw) /\
      Setoid.ker (interventionalProfile allowed interventionLaw) <=
        Setoid.ker (observationalProfile observationLaw) := by
  constructor
  · intro first second counterfactualsEqual
    funext action
    calc
      interventionLaw first action.1 =
          counterfactualLaw first (singleWorld action.1) :=
        (singleWorldLaw first action.1).symm
      _ = counterfactualLaw second (singleWorld action.1) := by
        exact congrFun counterfactualsEqual
          ⟨singleWorld action.1, singleWorldQueried action.1 action.2⟩
      _ = interventionLaw second action.1 := singleWorldLaw second action.1
  · intro first second interventionsEqual
    calc
      observationLaw first = interventionLaw first empty := (emptyLaw first).symm
      _ = interventionLaw second empty :=
        congrFun interventionsEqual ⟨empty, emptyAllowed⟩
      _ = observationLaw second := emptyLaw second
#print axioms causal_hierarchy_direction

/-- The stable and flip models show that the intervention kernel is not contained in the
counterfactual kernel. -/
theorem intervention_kernel_not_below_counterfactual :
    Not (Setoid.ker Int <= Setoid.ker CF) := by
  intro inclusion
  rcases finite_causal_query_hierarchy.2.2.2 with ⟨sameInterventions, differentCf⟩
  exact differentCf (inclusion sameInterventions)
#print axioms intervention_kernel_not_below_counterfactual

/-- The forward and reverse models show that the observation kernel is not contained in the
intervention kernel. -/
theorem observation_kernel_not_below_intervention :
    Not (Setoid.ker Obs <= Setoid.ker Int) := by
  intro inclusion
  rcases finite_causal_query_hierarchy.2.2.1 with ⟨sameObservations, differentInt⟩
  exact differentInt (inclusion sameObservations)
#print axioms observation_kernel_not_below_intervention

/-- Omitting the empty intervention can make the intervention profile constant while the
observational profile still separates the two Boolean models. -/
theorem empty_intervention_is_necessary :
    let observed : Bool -> Bool := id
    let intervened : Bool -> Option Unit -> Bool := fun model action =>
      match action with
      | none => model
      | some _ => false
    let allowed : Set (Option Unit) := {some ()}
    (forall model, intervened model none = observed model) /\
      none ∉ allowed /\
      Not (Setoid.ker (interventionalProfile allowed intervened) <=
        Setoid.ker (observationalProfile observed)) := by
  dsimp
  refine ⟨fun _ => rfl, by simp, ?_⟩
  intro inclusion
  apply Bool.false_ne_true
  apply inclusion
  funext action
  rcases action with ⟨action, actionAllowed⟩
  have action_eq : action = some () := by
    simpa using actionAllowed
  subst action
  rfl
#print axioms empty_intervention_is_necessary

/-- If the selected counterfactual family is empty, it can omit the sole single-world query
and have a universal kernel even though the intervention profile separates Boolean models. -/
theorem single_world_query_is_necessary :
    let allowed : Set Unit := Set.univ
    let queries : Set Unit := ∅
    let intervened : Bool -> Unit -> Bool := fun model _ => model
    let counterfactual : Bool -> Unit -> Bool := fun model _ => model
    let singleWorld : Unit -> Unit := id
    (forall model action,
      counterfactual model (singleWorld action) = intervened model action) /\
      (forall action, action ∈ allowed) /\
      (forall action, singleWorld action ∉ queries) /\
      Not (Setoid.ker (counterfactualProfile queries counterfactual) <=
        Setoid.ker (interventionalProfile allowed intervened)) := by
  dsimp
  refine ⟨fun _ _ => rfl, by simp, by simp, ?_⟩
  intro inclusion
  apply Bool.false_ne_true
  have sameInterventions := inclusion (x := false) (y := true) (by
    funext query
    exact False.elim ((Set.mem_empty_iff_false query.1).mp query.2))
  exact congrFun sameInterventions ⟨(), by simp⟩
#print axioms single_world_query_is_necessary

/-- With only the empty intervention and its one single-world query, the three kernels
coincide whenever the two law-identification equations hold. -/
theorem singleton_query_families_collapse
    {Model : Type uModel} {Law : Type uLaw}
    (observationLaw : Model -> Law) (interventionLaw : Model -> Unit -> Law)
    (counterfactualLaw : Model -> Unit -> Law)
    (emptyLaw : forall model, interventionLaw model () = observationLaw model)
    (singleWorldLaw : forall model,
      counterfactualLaw model () = interventionLaw model ()) :
    Setoid.ker
        (counterfactualProfile (Set.univ : Set Unit) counterfactualLaw) =
      Setoid.ker (interventionalProfile (Set.univ : Set Unit) interventionLaw) /\
    Setoid.ker (interventionalProfile (Set.univ : Set Unit) interventionLaw) =
      Setoid.ker (observationalProfile observationLaw) := by
  constructor
  · apply le_antisymm
    · intro first second sameCounterfactuals
      funext action
      rcases action with ⟨action, _⟩
      cases action
      calc
        interventionLaw first () = counterfactualLaw first () :=
          (singleWorldLaw first).symm
        _ = counterfactualLaw second () :=
          congrFun sameCounterfactuals ⟨(), by simp⟩
        _ = interventionLaw second () := singleWorldLaw second
    · intro first second sameInterventions
      funext query
      rcases query with ⟨query, _⟩
      cases query
      calc
        counterfactualLaw first () = interventionLaw first () := singleWorldLaw first
        _ = interventionLaw second () := congrFun sameInterventions ⟨(), by simp⟩
        _ = counterfactualLaw second () := (singleWorldLaw second).symm
  · apply le_antisymm
    · intro first second sameInterventions
      calc
        observationLaw first = interventionLaw first () := (emptyLaw first).symm
        _ = interventionLaw second () := congrFun sameInterventions ⟨(), by simp⟩
        _ = observationLaw second := emptyLaw second
    · intro first second sameObservations
      funext action
      rcases action with ⟨action, _⟩
      cases action
      calc
        interventionLaw first () = observationLaw first := emptyLaw first
        _ = observationLaw second := sameObservations
        _ = interventionLaw second () := (emptyLaw second).symm
#print axioms singleton_query_families_collapse

/-- A one-point visible law space makes every profile constant, for arbitrary model and query
types; hence all three kernels coincide. -/
theorem unit_law_space_collapses
    {Model : Type uModel} {Action : Type uAction} {Query : Type uQuery}
    (allowed : Set Action) (queries : Set Query)
    (observationLaw : Model -> Unit) (interventionLaw : Model -> Action -> Unit)
    (counterfactualLaw : Model -> Query -> Unit) :
    Setoid.ker (counterfactualProfile queries counterfactualLaw) =
        Setoid.ker (interventionalProfile allowed interventionLaw) /\
      Setoid.ker (interventionalProfile allowed interventionLaw) =
        Setoid.ker (observationalProfile observationLaw) := by
  constructor
  · apply le_antisymm
    · intro _ _ _
      exact Subsingleton.elim _ _
    · intro _ _ _
      exact Subsingleton.elim _ _
  · apply le_antisymm
    · intro _ _ _
      exact Subsingleton.elim _ _
    · intro _ _ _
      exact Subsingleton.elim _ _
#print axioms unit_law_space_collapses

/- Empty-type and `n = 0` audit: there are no model pairs on `Fin 0`, so all profile
kernels agree vacuously. -/
example (observation intervention counterfactual : Fin 0 -> Bool) :
    Setoid.ker counterfactual = Setoid.ker intervention /\
      Setoid.ker intervention = Setoid.ker observation := by
  constructor
  · apply Setoid.ext
    intro first _
    exact Fin.elim0 first
  · apply Setoid.ext
    intro first _
    exact Fin.elim0 first

/- No-randomness audit: regard each Boolean result as its point-mass law. Counterfactual and
interventional equivalence then coincide here, but observational equivalence remains coarser. -/
example :
    let observationLaw : Bool -> Bool := fun _ => false
    let interventionLaw : Bool -> Option Unit -> Bool := fun model action =>
      match action with
      | none => false
      | some _ => model
    let counterfactualLaw := interventionLaw
    Setoid.ker
        (counterfactualProfile (Set.univ : Set (Option Unit)) counterfactualLaw) =
      Setoid.ker
        (interventionalProfile (Set.univ : Set (Option Unit)) interventionLaw) /\
    Setoid.ker
        (interventionalProfile (Set.univ : Set (Option Unit)) interventionLaw) ≠
      Setoid.ker (observationalProfile observationLaw) := by
  dsimp
  constructor
  · rfl
  · intro kernelsEqual
    have sameInterventions :
        Setoid.ker
            (interventionalProfile (Set.univ : Set (Option Unit))
              fun model action => match action with
                | none => false
                | some _ => model)
            false true := by
      rw [kernelsEqual]
      rfl
    have false_eq_true := congrFun sameInterventions ⟨some (), by simp⟩
    exact Bool.false_ne_true false_eq_true

end D5.S3.ConceptDynamics.Causal.ThreeLayerCausalObservationLanguage
