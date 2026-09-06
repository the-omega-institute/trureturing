/- GID: D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite parent-indexed intervention traces compile sound exogenous dependency sets, shrink them under added constant interventions, and certify counterfactual query descent through source-coordinate restriction. -/

import D5.S3.ConceptDynamics.Causal.ParentOrderedStructuralEvaluationSemantics
import Mathlib.Logic.Function.DependsOn

/- Library audit (2026-09-05): the parent-indexed StructuralModel and
   EvaluationWitness are reused without a second structural evaluator.
   The pinned Mathlib DependsOn and dependsOn_iff_factorsThrough provide
   the semantic locality and kernel-descent notions. Compiled supports are
   conservative; failure of disjointness does not prove dependence.
   Interventions here assign constants independent of the exogenous state. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PartialIdentification.InterventionExogenousLocality

open D5.S3.ConceptDynamics.Causal.ParentOrderedStructuralEvaluationSemantics

variable {n : Nat} {Source Value Noise : Type*} [DecidableEq Source]

/-- Each parent-indexed equation reads only its declared exogenous coordinates
when its parent values are fixed. Parent locality is already enforced by type. -/
def ExogenousLocality
    (model : StructuralModel n Value (Source → Noise))
    (direct : Fin n → Finset Source) : Prop :=
  ∀ (v : Fin n) (parentValues : model.parents v → Value),
    DependsOn (model.equation v parentValues) (direct v : Set Source)

/-- A constant intervention removes the entire incoming dependency set. -/
def equationSupport
    (parents : Fin n → Finset (Fin n))
    (direct : Fin n → Finset Source) (intervention : Finset (Fin n))
    (prior : Fin n → Finset Source) (v : Fin n) : Finset Source :=
  if v ∈ intervention then ∅ else direct v ∪ (parents v).biUnion prior

/-- The support transfer updates exactly the coordinate updated by the trace. -/
def stepSupport
    (parents : Fin n → Finset (Fin n))
    (direct : Fin n → Finset Source) (intervention : Finset (Fin n))
    (prior : Fin n → Finset Source) (v : Fin n) : Fin n → Finset Source :=
  Function.update prior v (equationSupport parents direct intervention prior v)

/-- Propagate supports along the same finite list as the structural trace. -/
def traceSupport
    (parents : Fin n → Finset (Fin n))
    (direct : Fin n → Finset Source) (intervention : Finset (Fin n)) :
    List (Fin n) → (Fin n → Finset Source) → Fin n → Finset Source
  | [], prior => prior
  | v :: remaining, prior =>
      traceSupport parents direct intervention remaining
        (stepSupport parents direct intervention prior v)

private theorem equation_dependency_sound
    (model : StructuralModel n Value (Source → Noise))
    (direct : Fin n → Finset Source) (locality : ExogenousLocality model direct)
    (intervention : Finset (Fin n)) (assigned : Fin n → Value)
    (state : (Source → Noise) → Fin n → Value)
    (prior : Fin n → Finset Source)
    (state_local : ∀ v, DependsOn (fun u => state u v) (prior v : Set Source))
    (v : Fin n) :
    DependsOn (fun u => intervenedEquation model intervention assigned v (state u) u)
      (equationSupport model.parents direct intervention prior v : Set Source) := by
  intro u u' same
  by_cases intervened : v ∈ intervention
  · simp [intervenedEquation, intervened]
  · have same_source : ∀ i ∈ direct v, u i = u' i := by
      intro i hi
      apply same i
      change i ∈ equationSupport model.parents direct intervention prior v
      simp only [equationSupport, intervened, if_false]
      exact Finset.mem_union_left _ hi
    have same_parents :
        (fun p : model.parents v => state u p.1) =
          (fun p : model.parents v => state u' p.1) := by
      funext p
      apply state_local p.1
      intro i hi
      apply same i
      change i ∈ equationSupport model.parents direct intervention prior v
      simp only [equationSupport, intervened, if_false]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p.1, p.2, hi⟩)
    simp only [intervenedEquation, intervened, if_false]
    rw [same_parents]
    exact locality v (fun p => state u' p.1) same_source

private theorem step_dependency_sound
    (model : StructuralModel n Value (Source → Noise))
    (direct : Fin n → Finset Source) (locality : ExogenousLocality model direct)
    (intervention : Finset (Fin n)) (assigned : Fin n → Value)
    (state : (Source → Noise) → Fin n → Value)
    (prior : Fin n → Finset Source)
    (state_local : ∀ v, DependsOn (fun u => state u v) (prior v : Set Source))
    (v w : Fin n) :
    DependsOn
      (fun u => Function.update (state u) v
        (intervenedEquation model intervention assigned v (state u) u) w)
      (stepSupport model.parents direct intervention prior v w : Set Source) := by
  by_cases same : w = v
  · subst w
    simpa only [stepSupport, Function.update_self] using
      equation_dependency_sound model direct locality intervention assigned state prior state_local v
  · simpa only [stepSupport, Function.update_of_ne same] using state_local w

private theorem trace_dependency_sound
    (model : StructuralModel n Value (Source → Noise))
    (direct : Fin n → Finset Source) (locality : ExogenousLocality model direct)
    (intervention : Finset (Fin n)) (assigned : Fin n → Value)
    (remaining : List (Fin n))
    (state result : (Source → Noise) → Fin n → Value)
    (prior : Fin n → Finset Source)
    (state_local : ∀ v, DependsOn (fun u => state u v) (prior v : Set Source))
    (evaluates : ∀ u,
      EvaluationWitness model intervention assigned u remaining (state u) (result u)) :
    ∀ v, DependsOn (fun u => result u v)
      (traceSupport model.parents direct intervention remaining prior v : Set Source) := by
  induction remaining generalizing state prior with
  | nil =>
      intro v u u' same
      show result u v = result u' v
      have first : result u = state u := evaluates u
      have second : result u' = state u' := evaluates u'
      rw [first, second]
      exact state_local v same
  | cons v remaining ih =>
      let next : (Source → Noise) → Fin n → Value := fun u =>
        Function.update (state u) v
          (intervenedEquation model intervention assigned v (state u) u)
      have next_local : ∀ w, DependsOn (fun u => next u w)
          (stepSupport model.parents direct intervention prior v w : Set Source) :=
        step_dependency_sound model direct locality intervention assigned state prior state_local v
      have tail : ∀ u,
          EvaluationWitness model intervention assigned u remaining (next u) (result u) := by
        intro u
        rcases evaluates u with ⟨_, nextState, next_eq, tail⟩
        rw [next_eq] at tail
        exact tail
      exact ih next (stepSupport model.parents direct intervention prior v) next_local tail

/-- Select the unique response already supplied by the canonical parent-ordered
semantics. This adds no new evaluation relation or structural assumption. -/
noncomputable def evaluatedResponse
    (model : StructuralModel n Value (Source → Noise)) (topological : TopologicalOrder model)
    (intervention : Finset (Fin n)) (assigned : Fin n → Value)
    (u : Source → Noise) : Fin n → Value :=
  Classical.choose
    (parent_ordered_structure_evaluation_semantics model topological intervention assigned u).exists

/-- The selected response satisfies the existing evaluation relation. -/
theorem evaluatedResponse_spec
    (model : StructuralModel n Value (Source → Noise)) (topological : TopologicalOrder model)
    (intervention : Finset (Fin n)) (assigned : Fin n → Value) (u : Source → Noise) :
    EvaluationWitness model intervention assigned u model.order (model.initial u)
      (evaluatedResponse model topological intervention assigned u) :=
  Classical.choose_spec
    (parent_ordered_structure_evaluation_semantics model topological intervention assigned u).exists

/-- Initially every source is allowed. Thus arbitrary exogenous dependence of
model.initial is accounted for, rather than silently discarded. -/
def compiledSupport [Fintype Source]
    (model : StructuralModel n Value (Source → Noise))
    (direct : Fin n → Finset Source) (intervention : Finset (Fin n)) :
    Fin n → Finset Source :=
  traceSupport model.parents direct intervention model.order (fun _ => Finset.univ)

/-- Every evaluated intervention response descends through its compiled source
restriction. The proof propagates semantic locality along the actual trace. -/
theorem evaluatedResponse_dependsOn [Fintype Source]
    (model : StructuralModel n Value (Source → Noise)) (topological : TopologicalOrder model)
    (direct : Fin n → Finset Source) (locality : ExogenousLocality model direct)
    (intervention : Finset (Fin n)) (assigned : Fin n → Value) (v : Fin n) :
    DependsOn (fun u => evaluatedResponse model topological intervention assigned u v)
      (compiledSupport model direct intervention v : Set Source) := by
  apply trace_dependency_sound model direct locality intervention assigned model.order
    model.initial (evaluatedResponse model topological intervention assigned)
    (fun _ => Finset.univ)
  · intro w
    simpa only [Finset.coe_univ] using dependsOn_univ (fun u => model.initial u w)
  · exact evaluatedResponse_spec model topological intervention assigned

private theorem stepSupport_antitone_intervention
    (parents : Fin n → Finset (Fin n)) (direct : Fin n → Finset Source)
    (smaller larger : Finset (Fin n)) (interventions : smaller ⊆ larger)
    (old new : Fin n → Finset Source) (supports : ∀ w, new w ⊆ old w)
    (v w : Fin n) :
    stepSupport parents direct larger new v w ⊆ stepSupport parents direct smaller old v w := by
  by_cases same : w = v
  · subst w
    simp only [stepSupport, Function.update_self]
    by_cases fixed : v ∈ larger
    · simp [equationSupport, fixed]
    · have not_fixed : v ∉ smaller := fun h => fixed (interventions h)
      simp only [equationSupport, fixed, not_fixed, if_false]
      intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact Finset.mem_union_left _ hi
      · rcases Finset.mem_biUnion.mp hi with ⟨p, hp, hi⟩
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p, hp, supports p hi⟩)
  · simpa only [stepSupport, Function.update_of_ne same] using supports w

private theorem traceSupport_antitone_intervention
    (parents : Fin n → Finset (Fin n)) (direct : Fin n → Finset Source)
    (smaller larger : Finset (Fin n)) (interventions : smaller ⊆ larger)
    (remaining : List (Fin n)) (old new : Fin n → Finset Source)
    (supports : ∀ w, new w ⊆ old w) :
    ∀ w, traceSupport parents direct larger remaining new w ⊆
      traceSupport parents direct smaller remaining old w := by
  induction remaining generalizing old new with
  | nil => exact supports
  | cons v remaining ih =>
      exact ih (stepSupport parents direct smaller old v)
        (stepSupport parents direct larger new v)
        (stepSupport_antitone_intervention parents direct smaller larger interventions old new supports v)

/-- Adding constant interventions can only remove compiled exogenous
coordinates. This concerns dependency supports, not monotonicity of query values. -/
theorem compiledSupport_antitone_intervention [Fintype Source]
    (model : StructuralModel n Value (Source → Noise))
    (direct : Fin n → Finset Source)
    (smaller larger : Finset (Fin n)) (interventions : smaller ⊆ larger) (v : Fin n) :
    compiledSupport model direct larger v ⊆ compiledSupport model direct smaller v := by
  exact traceSupport_antitone_intervention model.parents direct smaller larger interventions
    model.order (fun _ => Finset.univ) (fun _ => Finset.univ) (fun _ _ hi => hi) v

/-- All queried worlds reuse the same exogenous assignment. Their safe query
support is the union of the queried coordinates' compiled supports. -/
def counterfactualSupport [Fintype Source]
    {Query : Type*} [Fintype Query]
    (model : StructuralModel n Value (Source → Noise)) (direct : Fin n → Finset Source)
    (interventions : Query → Finset (Fin n)) (observed : Query → Fin n) : Finset Source :=
  Finset.univ.biUnion (fun q => compiledSupport model direct (interventions q) (observed q))

/-- Joint unnested counterfactual readout on the original exogenous state space. -/
noncomputable def counterfactualReadout
    {Query : Type*}
    (model : StructuralModel n Value (Source → Noise)) (topological : TopologicalOrder model)
    (interventions : Query → Finset (Fin n)) (assigned : Query → Fin n → Value)
    (observed : Query → Fin n) (u : Source → Noise) : Query → Value :=
  fun q => evaluatedResponse model topological (interventions q) (assigned q) u (observed q)

/-- The finite vector of potential outcomes depends only on the union of its
intervention-specific supports. No independent noise copy is created per world. -/
theorem counterfactualReadout_dependsOn [Fintype Source]
    {Query : Type*} [Fintype Query]
    (model : StructuralModel n Value (Source → Noise)) (topological : TopologicalOrder model)
    (direct : Fin n → Finset Source) (locality : ExogenousLocality model direct)
    (interventions : Query → Finset (Fin n)) (assigned : Query → Fin n → Value)
    (observed : Query → Fin n) :
    DependsOn (counterfactualReadout model topological interventions assigned observed)
      (counterfactualSupport model direct interventions observed : Set Source) := by
  intro u u' same
  funext q
  apply evaluatedResponse_dependsOn model topological direct locality (interventions q) (assigned q)
    (observed q)
  intro i hi
  exact same i (Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ q, hi⟩)

/-- Every Boolean event on the finite counterfactual readout factors through
source-coordinate restriction in Mathlib's existing kernel-descent sense. -/
theorem counterfactualEvent_factorsThrough [Fintype Source]
    {Query : Type*} [Fintype Query]
    (model : StructuralModel n Value (Source → Noise)) (topological : TopologicalOrder model)
    (direct : Fin n → Finset Source) (locality : ExogenousLocality model direct)
    (interventions : Query → Finset (Fin n)) (assigned : Query → Fin n → Value)
    (observed : Query → Fin n) (event : (Query → Value) → Bool) :
    Function.FactorsThrough
      (fun u => event (counterfactualReadout model topological interventions assigned observed u))
      (counterfactualSupport model direct interventions observed : Set Source).domRestrict := by
  apply dependsOn_iff_factorsThrough.mp
  intro u u' same
  exact congrArg event
    (counterfactualReadout_dependsOn model topological direct locality interventions assigned observed same)

/-- In a four-node fork with roots 0 and 1 and outcomes 2 and 3, fixing root 1
leaves the common source 0, while also fixing root 0 removes that shared source.
This is a closed exact computation of the support transfer, not a dependence test. -/
theorem fork_support_cut_certificate :
    let parents : Fin 4 → Finset (Fin 4) := fun v => if v = 2 ∨ v = 3 then {0, 1} else ∅
    let direct : Fin 4 → Finset (Fin 4) := fun v => {v}
    let run := fun I => traceSupport parents direct I [0, 1, 2, 3] (fun _ => Finset.univ)
    run {1} 2 = {0, 2} ∧ run {1} 3 = {0, 3} ∧
      run {0, 1} 2 = {2} ∧ run {0, 1} 3 = {3} := by
  decide

#print axioms evaluatedResponse_dependsOn
#print axioms compiledSupport_antitone_intervention
#print axioms counterfactualReadout_dependsOn
#print axioms counterfactualEvent_factorsThrough
#print axioms fork_support_cut_certificate

end D5.S3.ConceptDynamics.PartialIdentification.InterventionExogenousLocality
