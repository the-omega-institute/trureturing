/- GID: D5/S3/ConceptDynamics/Agency/SelfFormationFreeWillBoundary
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Agency/SelfFormationFreeWillBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: History identity, voluntariness, and branching freedom obstruct reduction. -/

import D5.S0.Rewriting.Quotients.AnswerabilityCriterion
import D5.S3.ConceptDynamics.Fibers.BranchingFreedomNeedsRelation
import D5.S3.ConceptDynamics.MoralLuck.MoralLuckDescent

/- Library-search audit trail (2026-08-26):
   * Exact repository hit `moral_luck_descent_iff` proves factorization through a
     readout exactly when its fibres contain no unequal evaluations.
   * Exact repository hit `branching_process_is_not_functional` proves that a
     branching set-valued future has no functional representation.
   * No repository or pinned-Mathlib theorem combined current self-presentation,
     action voluntariness, and total future branching into one reduction boundary.
   * Pinned Mathlib hit `Set.eq_singleton_iff_nonempty_unique_mem` supplies the
     missing converse: a total nonbranching future is singleton-valued. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Agency.SelfFormationFreeWillBoundary

open D5.S3.ConceptDynamics.Fibers.BranchingFreedomNeedsRelation
open D5.S3.ConceptDynamics.MoralLuck.MoralLuckDescent
open D5.S0.Rewriting.Quotients.AnswerabilityCriterion

/-- A future relation is reductively deterministic when every history has exactly
the successor selected by one state-transition function. -/
def FunctionalFuture {History : Type*} (future : History -> Set History) : Prop :=
  exists step : History -> History, forall history, future history = {step history}

/-- Three independent obstructions to a reductive self-and-agency account:
current presentation loses identity, action loses voluntariness, or the future
relation has a genuine branch. -/
def SelfAgencyObstruction
    {History Present Identity Action Voluntariness : Type*}
    (present : History -> Present) (identity : History -> Identity)
    (action : History -> Action) (voluntariness : History -> Voluntariness)
    (future : History -> Set History) : Prop :=
  MoralLuckWitness present identity \/
    MoralLuckWitness action voluntariness \/
    BranchingFree future

/-- A reductive account recovers identity from current presentation,
voluntariness from the action result, and every future from one function. -/
def ReductiveSelfAgency
    {History Present Identity Action Voluntariness : Type*}
    (present : History -> Present) (identity : History -> Identity)
    (action : History -> Action) (voluntariness : History -> Voluntariness)
    (future : History -> Set History) : Prop :=
  ControlPrinciple present identity /\
    ControlPrinciple action voluntariness /\
    FunctionalFuture future

private theorem control_principle_iff_no_witness
    {History Readout Evaluation : Type*} [Nonempty History]
    (readout : History -> Readout) (evaluation : History -> Evaluation) :
    ControlPrinciple readout evaluation <->
      Not (MoralLuckWitness readout evaluation) := by
  let anchor : History := Classical.choice (inferInstance : Nonempty History)
  have criterion := answerability_criterion anchor readout evaluation
  constructor
  · intro hControl hWitness
    rcases hWitness with ⟨left, right, sameReadout, differentEvaluation⟩
    exact differentEvaluation (criterion.1.mp hControl sameReadout)
  · intro hNoWitness
    apply criterion.1.mpr
    intro left right sameReadout
    by_contra differentEvaluation
    exact hNoWitness ⟨left, right, sameReadout, differentEvaluation⟩

/-- For a total future relation, functional determinism is exactly absence of
branching. Totality is essential because an empty successor set does not branch
but cannot be a singleton graph. -/
theorem total_future_functional_iff_not_branching
    {History : Type*} (future : History -> Set History)
    (totalFuture : forall history, (future history).Nonempty) :
    FunctionalFuture future <-> Not (BranchingFree future) := by
  constructor
  · rintro ⟨step, hStep⟩ hBranch
    exact branching_process_is_not_functional future hBranch ⟨step, hStep⟩
  · intro hNoBranch
    classical
    let step : History -> History :=
      fun history => Classical.choose (totalFuture history)
    refine ⟨step, fun history => ?_⟩
    apply Set.eq_singleton_iff_unique_mem.mpr
    have hStep : step history ∈ future history := by
      exact Classical.choose_spec (totalFuture history)
    refine ⟨hStep, ?_⟩
    intro next hNext
    by_contra different
    exact hNoBranch ⟨history, step history, next, hStep, hNext, Ne.symm different⟩

/-- In an inhabited model, the whole self-and-agency account is reductive
exactly when none of the three explicit obstructions occurs. -/
theorem reductive_self_agency_iff_no_obstruction
    {History Present Identity Action Voluntariness : Type*}
    [Nonempty History]
    (present : History -> Present) (identity : History -> Identity)
    (action : History -> Action) (voluntariness : History -> Voluntariness)
    (future : History -> Set History)
    (totalFuture : forall history, (future history).Nonempty) :
    ReductiveSelfAgency present identity action voluntariness future <->
      Not (SelfAgencyObstruction present identity action voluntariness future) := by
  change
    (ControlPrinciple present identity /\
      ControlPrinciple action voluntariness /\
      FunctionalFuture future) <->
    Not (MoralLuckWitness present identity \/
      MoralLuckWitness action voluntariness \/
      BranchingFree future)
  constructor
  · rintro ⟨identityReduction, voluntaryReduction, functionalFuture⟩ obstruction
    rcases obstruction with identityWitness | voluntaryWitness | branch
    · exact (control_principle_iff_no_witness present identity).mp
        identityReduction identityWitness
    · exact (control_principle_iff_no_witness action voluntariness).mp
        voluntaryReduction voluntaryWitness
    · exact (total_future_functional_iff_not_branching future totalFuture).mp
        functionalFuture branch
  · intro noObstruction
    refine ⟨
      (control_principle_iff_no_witness present identity).mpr ?_,
      (control_principle_iff_no_witness action voluntariness).mpr ?_,
      (total_future_functional_iff_not_branching future totalFuture).mpr ?_⟩
    · intro identityWitness
      exact noObstruction (Or.inl identityWitness)
    · intro voluntaryWitness
      exact noObstruction (Or.inr (Or.inl voluntaryWitness))
    · intro branch
      exact noObstruction (Or.inr (Or.inr branch))

/-- A concrete Boolean model witnesses that history-sensitive identity and
externally autonomous behaviour can coexist with functional determinism. -/
theorem history_sensitive_self_and_deterministic_autonomy_coexist :
    exists (present : Bool -> Unit) (identity : Bool -> Bool)
      (process : Bool -> Bool -> Set Bool) (step : Bool -> Bool),
      MoralLuckWitness present identity /\
        Not (ControlPrinciple present identity) /\
        AutonomousFree process /\
        (forall external history, process external history = {step history}) := by
  refine ⟨fun _ => (), id, fun _ history => {history}, id, ?_⟩
  have identityWitness : MoralLuckWitness (fun _ : Bool => ()) id :=
    ⟨false, true, rfl, Bool.false_ne_true⟩
  refine ⟨identityWitness, ?_, ?_, ?_⟩
  · intro identityReduction
    exact (control_principle_iff_no_witness (fun _ : Bool => ()) id).mp
      identityReduction identityWitness
  · exact ⟨false, true, Bool.false_ne_true, rfl⟩
  · intro external history
    rfl

#print axioms total_future_functional_iff_not_branching
#print axioms reductive_self_agency_iff_no_obstruction
#print axioms history_sensitive_self_and_deterministic_autonomy_coexist

end D5.S3.ConceptDynamics.Agency.SelfFormationFreeWillBoundary
