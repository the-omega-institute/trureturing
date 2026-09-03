/- GID: D5/S3/ConceptDynamics/Causal/PartialIdentification/PartialGraphCompletionRange
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PartialIdentification/PartialGraphCompletionRange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Partial-graph uncertainty forms a union of completion-specific sharp ranges; envelope endpoints remain exact while the full range may be disconnected. -/

import D5.S3.ConceptDynamics.Causal.NonconvexSharpIdentification
import Mathlib.Tactic

/- Library-search audit trail (2026-09-03):
   * `PartialGraphInformationOrder` proves antitonicity when graph information
     is refined, but does not characterize the range induced by several
     compatible complete graphs.
   * `NonconvexSharpIdentification` permits disconnected identified ranges but
     does not expose graph-completion semantics.
   * Repository searches found no theorem distinguishing epistemic union over
     candidate graphs from probabilistic mixture over graph indices.
   * This module formalizes the union semantics. Convexifying that union is a
     separate modelling assumption and may add unattainable query values. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PartialIdentification.PartialGraphCompletionRange

open D5.S3.ConceptDynamics.Causal.NonconvexSharpIdentification

/-- Every compatible complete graph, or more generally every structural
completion, carries its own sharp scalar interval. -/
structure CompletionSharpFamily (Completion : Type*) where
  attainable : Completion -> Real -> Prop
  lower : Completion -> Real
  upper : Completion -> Real
  lower_le_upper : forall completion,
    lower completion <= upper completion
  sharp : forall completion target,
    attainable completion target <->
      lower completion <= target /\ target <= upper completion

/-- A partial graph represents epistemic uncertainty over one compatible
completion. A query value is globally attainable when at least one completion
admits it. -/
def PartialGraphAttainable
    {Completion : Type*}
    (family : CompletionSharpFamily Completion)
    (target : Real) : Prop :=
  exists completion, family.attainable completion target

/-- The canonical nonconvex identification problem whose model records both a
completion and one attainable query value for that completion. -/
def completionUnionProblem
    {Completion : Type*}
    (family : CompletionSharpFamily Completion) :
    IdentificationProblem (Completion × Real) where
  feasible model := family.attainable model.1 model.2
  query model := model.2

/-- The exact identified range under partial-graph uncertainty is the union of
the completion-specific sharp intervals. -/
theorem partial_graph_range_is_completion_union
    {Completion : Type*}
    (family : CompletionSharpFamily Completion) :
    IsSharpRange
      (completionUnionProblem family)
      (fun target => exists completion,
        family.lower completion <= target /\
          target <= family.upper completion) := by
  intro target
  constructor
  · rintro ⟨completion, bounds⟩
    exact
      ⟨(completion, target),
        (family.sharp completion target).2 bounds,
        rfl⟩
  · rintro ⟨⟨completion, value⟩, attainable, value_eq⟩
    subst value
    exact
      ⟨completion,
        (family.sharp completion target).1 attainable⟩

/-- A value belongs to the partial-graph range exactly when it belongs to one
completion-specific interval. -/
theorem partial_graph_attainable_iff_interval_member
    {Completion : Type*}
    (family : CompletionSharpFamily Completion)
    (target : Real) :
    PartialGraphAttainable family target <->
      exists completion,
        family.lower completion <= target /\
          target <= family.upper completion := by
  constructor
  · rintro ⟨completion, attainable⟩
    exact ⟨completion, (family.sharp completion target).1 attainable⟩
  · rintro ⟨completion, bounds⟩
    exact ⟨completion, (family.sharp completion target).2 bounds⟩

/-- A lower envelope is exact for the completion union when it lies below every
completion-specific lower endpoint and is attained by one completion. -/
theorem exact_lower_endpoint_of_completion_envelope
    {Completion : Type*}
    (family : CompletionSharpFamily Completion)
    (globalLower : Real)
    (below_every_lower : forall completion,
      globalLower <= family.lower completion)
    (attained : exists completion,
      family.lower completion = globalLower) :
    IsExactLowerEndpoint
      (completionUnionProblem family) globalLower := by
  constructor
  · rintro ⟨completion, target⟩ feasible
    have bounds := (family.sharp completion target).1 feasible
    exact (below_every_lower completion).trans bounds.1
  · rcases attained with ⟨completion, endpoint_eq⟩
    refine ⟨(completion, globalLower), ?_, rfl⟩
    apply (family.sharp completion globalLower).2
    rw [endpoint_eq]
    exact ⟨le_rfl, family.lower_le_upper completion⟩

/-- The dual upper-envelope statement. -/
theorem exact_upper_endpoint_of_completion_envelope
    {Completion : Type*}
    (family : CompletionSharpFamily Completion)
    (globalUpper : Real)
    (above_every_upper : forall completion,
      family.upper completion <= globalUpper)
    (attained : exists completion,
      family.upper completion = globalUpper) :
    IsExactUpperEndpoint
      (completionUnionProblem family) globalUpper := by
  constructor
  · rintro ⟨completion, target⟩ feasible
    have bounds := (family.sharp completion target).1 feasible
    exact bounds.2.trans (above_every_upper completion)
  · rcases attained with ⟨completion, endpoint_eq⟩
    refine ⟨(completion, globalUpper), ?_, rfl⟩
    apply (family.sharp completion globalUpper).2
    rw [endpoint_eq]
    exact ⟨family.lower_le_upper completion, le_rfl⟩

/-- Two candidate completions with singleton ranges zero and two. -/
def twoCompletionFamily : CompletionSharpFamily Bool where
  attainable completion target :=
    target = if completion then 2 else 0
  lower completion := if completion then 2 else 0
  upper completion := if completion then 2 else 0
  lower_le_upper := by intro completion; exact le_rfl
  sharp := by
    intro completion target
    cases completion with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        constructor
        · intro target_eq
          subst target
          exact ⟨le_rfl, le_rfl⟩
        · intro bounds
          linarith
    | true =>
        simp only [if_true]
        constructor
        · intro target_eq
          subst target
          exact ⟨le_rfl, le_rfl⟩
        · intro bounds
          linarith

/-- The completion-union endpoints are exactly zero and two, while the value
one remains unattainable. Hence replacing graph uncertainty by the envelope
interval changes the identified set. -/
theorem partial_graph_envelope_need_not_be_sharp_interval :
    IsExactLowerEndpoint
        (completionUnionProblem twoCompletionFamily) 0 /\
      IsExactUpperEndpoint
        (completionUnionProblem twoCompletionFamily) 2 /\
      ¬IsSharpInterval
        (completionUnionProblem twoCompletionFamily) 0 2 := by
  constructor
  · exact exact_lower_endpoint_of_completion_envelope
      twoCompletionFamily 0
      (by intro completion; cases completion <;> norm_num)
      ⟨false, by simp [twoCompletionFamily]⟩
  constructor
  · exact exact_upper_endpoint_of_completion_envelope
      twoCompletionFamily 2
      (by intro completion; cases completion <;> norm_num)
      ⟨true, by simp [twoCompletionFamily]⟩
  · intro sharpInterval
    have one_realized :=
      (sharpInterval 1).mp ⟨by norm_num, by norm_num⟩
    rcases one_realized with
      ⟨⟨completion, target⟩, feasible, target_eq⟩
    subst target
    cases completion <;> simp [twoCompletionFamily] at feasible

#print axioms partial_graph_range_is_completion_union
#print axioms exact_lower_endpoint_of_completion_envelope
#print axioms exact_upper_endpoint_of_completion_envelope
#print axioms partial_graph_envelope_need_not_be_sharp_interval

end D5.S3.ConceptDynamics.Causal.PartialIdentification.PartialGraphCompletionRange
