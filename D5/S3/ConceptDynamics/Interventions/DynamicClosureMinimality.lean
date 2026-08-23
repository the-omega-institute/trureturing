/- GID: D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interventions/DynamicClosureMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite intervention traces form the least intervention-closed concept refinement. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/- Library-search audit trail (2026-08-23):
   * `rg -n -F 'dynamic_closure_is_least' D5 Golden/Frozen/accepted` found no
     repository declaration or accepted duplicate.
   * The requested dynamic-closure search found `PredictionClosureDynamicalRepair`
     and `ObserverOrbitClosure`; they concern a finite-dimensional linear operator,
     not an arbitrary intervention family acting on concept fibers.
   * `ControlledFiniteStability` proves a finite-state greatest stable-equivalence
     result. `InterventionNaturalityMinimality` and
     `controlled_behavior_universal_property` additionally assume finite carriers,
     a surjective realization, and explicit commuting realized transitions.
   * The exact upstream trajectory primitives `runWord` and `controlledBehavior`,
     and the canonical factorization order `Refines`, are imported and reused.
   * Pinned Mathlib has `ClosureOperator`, `OrderHom.lfp`, `Function.extend`, and
     `Function.factorsThrough_iff`. The first two would require replacing concepts
     by a relation lattice; `Function.extend` supplies the needed total factor. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Interventions.DynamicClosureMinimality

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/-- A concept is closed under an intervention family when each intervention
preserves every fiber of the concept readout. -/
def InterventionClosed {X A U : Type*} (concept : Concept X A)
    (intervene : U -> X -> X) : Prop :=
  forall u x y, concept x = concept y ->
    concept (intervene u x) = concept (intervene u y)

/-- The dynamic closure records the original concept after every finite word of
interventions. -/
def DynClosure {X A U : Type*} (concept : Concept X A)
    (intervene : U -> X -> X) : Concept X (List U -> A) :=
  controlledBehavior intervene concept

/-- The dynamic closure refines the original concept via the empty word. -/
theorem concept_refines_dynamic_closure {X A U : Type*}
    (concept : Concept X A) (intervene : U -> X -> X) :
    Refines concept (DynClosure concept intervene) := by
  refine ⟨fun behavior => behavior [], ?_⟩
  funext x
  rfl

/-- Every intervention preserves the fibers of the dynamic closure. -/
theorem dynamic_closure_is_intervention_closed {X A U : Type*}
    (concept : Concept X A) (intervene : U -> X -> X) :
    InterventionClosed (DynClosure concept intervene) intervene := by
  intro u x y historiesEqual
  funext word
  exact congrFun historiesEqual (u :: word)

private theorem runWord_preserves_fiber {X B U : Type*}
    (candidate : Concept X B) (intervene : U -> X -> X)
    (closed : InterventionClosed candidate intervene) :
    forall word x y, candidate x = candidate y ->
      candidate (runWord intervene word x) = candidate (runWord intervene word y) := by
  intro word
  induction word with
  | nil =>
      intro x y equal
      exact equal
  | cons u word inductionHypothesis =>
      intro x y equal
      exact inductionHypothesis (intervene u x) (intervene u y) (closed u x y equal)

/-- Any intervention-closed concept refining the original concept also refines
its dynamic closure, so the dynamic closure is the least such refinement. -/
theorem dynamic_closure_is_least {X A U B : Type*}
    (concept : Concept X A) (intervene : U -> X -> X) (candidate : Concept X B)
    (refinement : Refines concept candidate)
    (closed : InterventionClosed candidate intervene) :
    Refines (DynClosure concept intervene) candidate := by
  rcases refinement with ⟨forget, conceptFactors⟩
  have closureFactors :
      Function.FactorsThrough (DynClosure concept intervene) candidate := by
    intro x y equal
    funext word
    have candidateEqual :=
      runWord_preserves_fiber candidate intervene closed word x y equal
    change concept (runWord intervene word x) = concept (runWord intervene word y)
    rw [conceptFactors]
    exact congrArg forget candidateEqual
  refine
    ⟨Function.extend candidate (DynClosure concept intervene)
      (fun value _ => forget value), ?_⟩
  exact (closureFactors.extend_comp (fun value _ => forget value)).symm

/-- The dynamic closure carrier and its defining concept are concretely inhabited. -/
example : Nonempty (Concept Bool (List Unit -> Bool)) :=
  ⟨DynClosure id (fun _ => Bool.not)⟩

/-- Two Boolean flips return the dynamic closure trace to its initial value. -/
example : DynClosure id (fun _ : Unit => Bool.not) false [(), ()] = false := by
  rfl

#print axioms dynamic_closure_is_least

end D5.S3.ConceptDynamics.Interventions.DynamicClosureMinimality
