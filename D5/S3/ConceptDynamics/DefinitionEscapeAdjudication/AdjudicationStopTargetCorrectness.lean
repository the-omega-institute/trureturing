/- GID: D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/AdjudicationStopTargetCorrectness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeAdjudication/AdjudicationStopTargetCorrectness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact finite adjudication stop checking and guarded boundary behavior. -/

import D5.S3.ConceptDynamics.DefinitionEscapeAdjudication.ParetoFrontierStopDivergence
import Mathlib.Data.Bool.Basic

/- Library-search audit trail (2026-08-28):
   * Exact D5 searches for `OrientedStopOnDecisionSet`, `OrientedStop`,
     `stopCheck`, and `settleStop` found no declarations. The frozen
     `ParetoFrontierStopDivergence` supplies `OrientationSpec`, `DecisionSet`,
     and the independently defined `AdjudicationStopTargetOnDecisionSet`.
   * Pinned-Mathlib searches for `any_eq_true`, `decide_eq_true`, and finite
     Boolean scans found the generic `Bool.decide_iff` and list quantifier
     lemmas. The checker below instead uses decidable propositions bounded by
     `D.feasible`, preserving the source's ordered failure branches directly.
   * GitHub code searches for `AdjudicationStopTarget` and
     `OrientedStopOnDecisionSet` in Lean returned no hits. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

open D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion

universe u

/-- The source's oriented stop predicate, expanded independently from the
frozen named adjudication target. -/
def OrientedStopOnDecisionSet
    {Goal Action Source Version Scope : Type u}
    [DecidableEq Action]
    (AdmTarget : Goal -> Set Action)
    (InScope : Scope -> Action -> Prop)
    (O : OrientationSpec Goal Action Source Version Scope AdmTarget InScope)
    (D : DecisionSet Action) : Prop :=
  exists current, D.current = some current ∧ current ∈ D.feasible ∧
    (forall a, a ∈ D.feasible ->
      a ∈ AdmTarget O.goal ∧ InScope O.scope a) ∧
    ¬ exists a, a ∈ D.feasible ∧ O.relation current a ∧
      ¬ O.relation a current

/-- The commitment-level oriented stop reads only the sealed decision set. -/
def OrientedStop
    {Goal Source Version Scope EventId Evidence Round Action Time TargetChain
      Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Action]
    (AdmTarget : Goal -> Set Action)
    (InScope : Scope -> Action -> Prop)
    (O : OrientationSpec Goal Action Source Version Scope AdmTarget InScope)
    {n : Round}
    (K : ProspectiveCommitment EventId Evidence Round Action Time TargetChain
      Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n) : Prop :=
  OrientedStopOnDecisionSet AdmTarget InScope O K.decision

/-- The named commitment-level target is the frozen decision-set target at the
commitment's sealed decision coordinate. -/
def AdjudicationStopTarget
    {Goal Source Version Scope EventId Evidence Round Action Time TargetChain
      Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Action]
    (AdmTarget : Goal -> Set Action)
    (InScope : Scope -> Action -> Prop)
    (O : OrientationSpec Goal Action Source Version Scope AdmTarget InScope)
    {n : Round}
    (K : ProspectiveCommitment EventId Evidence Round Action Time TargetChain
      Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n) : Prop :=
  AdjudicationStopTargetOnDecisionSet AdmTarget InScope O K.decision

/-- Ordered finite stop scan: missing or infeasible current, an invalid domain
member, and a strict successor are rejected in that order. -/
def stopCheck
    {Goal Action Source Version Scope : Type u}
    [DecidableEq Action]
    (AdmTarget : Goal -> Set Action)
    (InScope : Scope -> Action -> Prop)
    (O : OrientationSpec Goal Action Source Version Scope AdmTarget InScope)
    (D : DecisionSet Action)
    [forall a, Decidable (a ∈ AdmTarget O.goal)]
    [forall a, Decidable (InScope O.scope a)]
    [forall a b, Decidable (O.relation a b)] : Bool :=
  match D.current with
  | none => false
  | some current =>
      if current ∉ D.feasible then
        false
      else if exists a, a ∈ D.feasible ∧
          (a ∉ AdmTarget O.goal ∨ ¬ InScope O.scope a) then
        false
      else if exists a, a ∈ D.feasible ∧ O.relation current a ∧
          ¬ O.relation a current then
        false
      else
        true

/-- The stop component of settlement depends only on the commitment decision
set and the supplied sourced orientation. -/
def settleStop
    {Goal Source Version Scope EventId Evidence Round Action Time TargetChain
      Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Action]
    (AdmTarget : Goal -> Set Action)
    (InScope : Scope -> Action -> Prop)
    (O : OrientationSpec Goal Action Source Version Scope AdmTarget InScope)
    {n : Round}
    (K : ProspectiveCommitment EventId Evidence Round Action Time TargetChain
      Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
    [forall a, Decidable (a ∈ AdmTarget O.goal)]
    [forall a, Decidable (InScope O.scope a)]
    [forall a b, Decidable (O.relation a b)] : Bool :=
  stopCheck AdmTarget InScope O K.decision

/-- The named stop target is exactly the existing oriented stop, its finite
checker is sound and complete, and missing, empty, or infeasible current data
cannot be accepted through vacuous quantification. -/
theorem adjudication_stop_target_correctness
    {Goal Action Source Version Scope : Type u}
    [DecidableEq Action]
    (AdmTarget : Goal -> Set Action)
    (InScope : Scope -> Action -> Prop)
    (O : OrientationSpec Goal Action Source Version Scope AdmTarget InScope)
    (D : DecisionSet Action)
    [forall a, Decidable (a ∈ AdmTarget O.goal)]
    [forall a, Decidable (InScope O.scope a)]
    [forall a b, Decidable (O.relation a b)]
    {EventId Evidence Round Time TargetChain Domain Epsilon Condition Comparator
      TestPlan Baseline WeightSpec : Type u}
    [LinearOrder EventId] [Preorder Time]
    {n : Round}
    (K : ProspectiveCommitment EventId Evidence Round Action Time TargetChain
      Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n) :
    (AdjudicationStopTargetOnDecisionSet AdmTarget InScope O D ↔
      OrientedStopOnDecisionSet AdmTarget InScope O D) ∧
    (AdjudicationStopTarget AdmTarget InScope O K ↔
      OrientedStop AdmTarget InScope O K) ∧
    (stopCheck AdmTarget InScope O D = true ↔
      AdjudicationStopTargetOnDecisionSet AdmTarget InScope O D) ∧
    (settleStop AdmTarget InScope O K = true ↔
      AdjudicationStopTarget AdmTarget InScope O K) ∧
    (settleStop AdmTarget InScope O K = false ↔
      ¬ AdjudicationStopTarget AdmTarget InScope O K) ∧
    (D.current = none ->
      ¬ AdjudicationStopTargetOnDecisionSet AdmTarget InScope O D) ∧
    (D.feasible = ∅ ->
      ¬ AdjudicationStopTargetOnDecisionSet AdmTarget InScope O D) ∧
    (forall a, D.current = some a ∧ a ∉ D.feasible ->
      ¬ AdjudicationStopTargetOnDecisionSet AdmTarget InScope O D) := by
  have targetIffOriented :
      AdjudicationStopTargetOnDecisionSet AdmTarget InScope O D ↔
        OrientedStopOnDecisionSet AdmTarget InScope O D := by
    rfl
  have commitmentIffOriented :
      AdjudicationStopTarget AdmTarget InScope O K ↔
        OrientedStop AdmTarget InScope O K := by
    rfl
  have checkerCorrectFor : forall D' : DecisionSet Action,
      stopCheck AdmTarget InScope O D' = true ↔
        AdjudicationStopTargetOnDecisionSet AdmTarget InScope O D' := by
    intro D'
    cases hcurrent : D'.current <;>
      simp [stopCheck, hcurrent, AdjudicationStopTargetOnDecisionSet]
  have checkerCorrect := checkerCorrectFor D
  have settlementCorrect :
      settleStop AdmTarget InScope O K = true ↔
        AdjudicationStopTarget AdmTarget InScope O K := by
    simpa [settleStop, AdjudicationStopTarget] using
      checkerCorrectFor K.decision
  have settlementRejects :
      settleStop AdmTarget InScope O K = false ↔
        ¬ AdjudicationStopTarget AdmTarget InScope O K := by
    rw [← settlementCorrect]
    exact Bool.eq_false_iff
  have missingCurrent : D.current = none ->
      ¬ AdjudicationStopTargetOnDecisionSet AdmTarget InScope O D := by
    intro hcurrent
    simp [AdjudicationStopTargetOnDecisionSet, hcurrent]
  have emptyFeasible : D.feasible = ∅ ->
      ¬ AdjudicationStopTargetOnDecisionSet AdmTarget InScope O D := by
    intro hfeasible
    simp [AdjudicationStopTargetOnDecisionSet, hfeasible]
  have infeasibleCurrent : forall a,
      D.current = some a ∧ a ∉ D.feasible ->
        ¬ AdjudicationStopTargetOnDecisionSet AdmTarget InScope O D := by
    rintro a ⟨hcurrent, notFeasible⟩
    simp [AdjudicationStopTargetOnDecisionSet, hcurrent, notFeasible]
  exact ⟨targetIffOriented, commitmentIffOriented, checkerCorrect,
    settlementCorrect, settlementRejects, missingCurrent, emptyFeasible,
    infeasibleCurrent⟩

private instance stopWitnessAdmissibleDecidable
    (goal : Unit) (action : ActionTwo) :
    Decidable (action ∈ admissibleTargetTwo goal) :=
  isTrue (Set.mem_univ action)

private instance stopWitnessScopeDecidable
    (scope : Unit) (action : ActionTwo) :
    Decidable (inScopeTwo scope action) :=
  isTrue True.intro

private instance stopWitnessStayRelationDecidable
    (a b : ActionTwo) : Decidable (stayOrientation.relation a b) := by
  change Decidable (a = b)
  infer_instance

private instance stopWitnessAdvanceRelationDecidable
    (a b : ActionTwo) : Decidable (advanceOrientation.relation a b) := by
  change Decidable (a.1 <= b.1)
  infer_instance

/-- The frozen two-action stay orientation supplies a compiling positive
checker witness for the theorem's decidable premises. -/
example :
    stopCheck admissibleTargetTwo inScopeTwo stayOrientation decisionTwo = true := by
  decide

/-- The same finite carrier under the advance orientation is rejected. -/
example :
    stopCheck admissibleTargetTwo inScopeTwo advanceOrientation decisionTwo = false := by
  decide

/-- The concrete decision domain remains inhabited independently of the stop
truth value. -/
example : ActionTwo := 0

#print axioms adjudication_stop_target_correctness

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
