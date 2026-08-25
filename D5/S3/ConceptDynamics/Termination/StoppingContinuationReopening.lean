/- GID: D5/S3/ConceptDynamics/Termination/StoppingContinuationReopening
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Termination/StoppingContinuationReopening
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed stages can close while changing targets repeatedly create new defects. -/

import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-25):
   * Type-shape search `rg -n 'Set \(X × X\)' D5 -g '*.lean'` found the
     canonical `defectRelation` in `RefinementRiskCostTradeoff` and its uses.
     It is imported below; no residual, escape, collision, or error set is
     redefined.
   * English/Chinese synonym searches for `closed|closure|completion|complete`,
     `reopen|reopening|open world|stagewise|local completion`, and
     `闭合|完成|重新打开|重开|开放世界|局部完成` found
     `TargetRecoveryCriterion`, `TargetClosureOperator`, and the frozen
     `OverreachWithoutLicense.domain_expansion_reopens_completion`. The first
     two concern factorization/target joins; the last is one finite strict
     scope expansion, not an open-world sequence with infinitely many genuine
     reopenings.
   * Synonym searches for `approximate|tolerance|deviation|precision|epsilon`,
     `budget|stop|stopping|gain|cost|supremum`, and
     `method|proposal|NoProposal` found no exact stopping declarations.
     `WeightedResidualCoverage` has an unrelated natural-number tolerance;
     `OverreachWithoutLicense` records a different section's missing abstract
     tolerance laws.
   * Neighbor-vocabulary commands `ls D5/S3/ConceptDynamics/Termination
     D5/S3/ConceptDynamics/Completion` and
     `git grep -n '^def \|^  def ' -- D5/S3/ConceptDynamics | head -60`
     found no reusable local-completion, open-world, method-stop, or
     budget-stop definition. The target path was absent before this edit.
   * Pinned-Mathlib search found `Real.sSup_empty`, which fixes `sSup ∅ = 0`,
     and `csSup_le_iff`, which characterizes an `sSup` upper bound for a
     nonempty bounded-above set. The total budget-stop definition therefore
     uses the pointwise form; `budget_stop_iff_sSup_le` applies
     `csSup_le_iff` under exactly its two public premises.
   * Pinned-Mathlib and Loogle searches for `Frequently` at `Filter.atTop`
     found `Filter.frequently_atTop`; it is applied directly to certify
     infinitely many reopenings. Loogle also returned `csSup_le_iff` as the
     exact conditional-supremum hit. Both LeanSearch HTTP queries returned
     404; no third-party exact theorem for the stagewise separation was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Termination.StoppingContinuationReopening

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- Target closure means exactly that the canonical target defect is empty. -/
def Closed {X Coordinate Target : Type*}
    (readout : Concept X Coordinate) (target : Concept X Target) : Prop :=
  defectRelation readout target = ∅

/-- Approximate closure compares a supplied deviation with the supplied
precision. No order laws beyond the comparison used by the source are added. -/
def ApproximatelyClosed {X Coordinate Target Delta : Type*} [LE Delta]
    (deviation : Concept X Coordinate -> Concept X Target -> Delta)
    (readout : Concept X Coordinate) (target : Concept X Target)
    (precision : Delta) : Prop :=
  deviation readout target ≤ precision

/-- Budget stopping in pointwise form. This is total even when no decision is
feasible, unlike the source's unqualified real supremum notation. -/
def BudgetStop {Decision Cost Gain Rate : Type*}
    [LE Cost] [HDiv Gain Cost Rate] [LE Rate]
    (cost : Decision -> Cost) (gain : Decision -> Gain)
    (budget : Cost) (threshold : Rate) : Prop :=
  ∀ decision, cost decision ≤ budget ->
    gain decision / cost decision ≤ threshold

/-- Method stopping says that the method returns the distinguished
`noProposal` value on the system and its supplied evidence input. -/
def MethodStopped {System Evidence Proposal : Type*}
    (method : System -> Evidence -> Proposal)
    (system : System) (evidence : Evidence) (noProposal : Proposal) : Prop :=
  method system evidence = noProposal

/-- The four parameters held fixed by local completion: object domain, target,
operation family, and precision. -/
structure LocalParameters
    (World Target Operation Precision : Type*) where
  objectDomain : Set World
  target : Concept World Target
  operationFamily : Set Operation
  precision : Precision

/-- A readout is locally complete at one fixed parameter quadruple exactly
when its restriction to that object domain is target-closed. -/
def LocallyComplete
    {World Coordinate Target Operation Precision : Type*}
    (parameters : LocalParameters World Target Operation Precision)
    (readout : Concept World Coordinate) : Prop :=
  Closed
    (fun object : ↑parameters.objectDomain => readout object.1)
    (fun object : ↑parameters.objectDomain => parameters.target object.1)

/-- At least one member of the local-completion parameter quadruple changes. -/
def LocalParametersChanged
    {World Target Operation Precision : Type*}
    (current next : LocalParameters World Target Operation Precision) : Prop :=
  current.objectDomain ≠ next.objectDomain ∨
    current.target ≠ next.target ∨
    current.operationFamily ≠ next.operationFamily ∨
    current.precision ≠ next.precision

/-- An open-world sequence changes at least one local parameter at every
adjacent stage; this is the source's persistent-change requirement. -/
def OpenWorldSequence
    {World Target Operation Precision : Type*}
    (parameters : Nat -> LocalParameters World Target Operation Precision) : Prop :=
  ∀ stage, LocalParametersChanged (parameters stage) (parameters (stage + 1))

/-- Reopening requires both a change in the object domain, target, precision,
operation family, or definition language and a nonempty canonical defect at
the new parameters. A harmless parameter change is therefore not a reopening. -/
def Reopens
    {World Coordinate Target Operation Precision Definition : Type*}
    (current next : LocalParameters World Target Operation Precision)
    (currentLanguage nextLanguage : Set Definition)
    (readout : Concept World Coordinate) : Prop :=
  (current.objectDomain ≠ next.objectDomain ∨
      current.target ≠ next.target ∨
      current.precision ≠ next.precision ∨
      current.operationFamily ≠ next.operationFamily ∨
      currentLanguage ≠ nextLanguage) ∧
    (defectRelation
      (fun object : ↑next.objectDomain => readout object.1)
      (fun object : ↑next.objectDomain => next.target object.1)).Nonempty

/-- On a nonempty feasible set with bounded-above real gain/cost ratios, the
total pointwise budget-stop definition is exactly the source's `sSup` formula. -/
theorem budget_stop_iff_sSup_le
    {Decision : Type*} (cost gain : Decision -> Real)
    (budget threshold : Real)
    (feasibleNonempty : ({decision | cost decision ≤ budget} : Set Decision).Nonempty)
    (ratiosBounded : BddAbove
      ((fun decision => gain decision / cost decision) ''
        {decision | cost decision ≤ budget})) :
    BudgetStop cost gain budget threshold ↔
      sSup ((fun decision => gain decision / cost decision) ''
        {decision | cost decision ≤ budget}) ≤ threshold := by
  rw [csSup_le_iff ratiosBounded (feasibleNonempty.image _)]
  constructor
  · intro stopped ratio ratioInImage
    rcases ratioInImage with ⟨decision, feasible, rfl⟩
    exact stopped decision feasible
  · intro everyRatio decision feasible
    exact everyRatio _ ⟨decision, feasible, rfl⟩

/-- There is an open-world sequence with nonempty stages that is complete at
every fixed parameter quadruple and nevertheless reopens infinitely often. -/
theorem stagewise_completion_with_infinite_reopening :
    ∃ (parameters : Nat -> LocalParameters Nat Bool Unit Nat)
      (languages : Nat -> Set Unit)
      (systems : Nat -> Concept Nat Bool),
      Nonempty Bool ∧
        (∀ stage, (parameters stage).objectDomain.Nonempty) ∧
        OpenWorldSequence parameters ∧
        (∀ stage, LocallyComplete (parameters stage) (systems stage)) ∧
        (∃ᶠ stage in Filter.atTop,
          Reopens (parameters stage) (parameters (stage + 1))
            (languages stage) (languages (stage + 1)) (systems stage)) := by
  let targetAt : Nat -> Concept Nat Bool :=
    fun stage object => decide (object = stage)
  let parameters : Nat -> LocalParameters Nat Bool Unit Nat := fun stage =>
    { objectDomain := Set.univ
      target := targetAt stage
      operationFamily := Set.univ
      precision := stage }
  let languages : Nat -> Set Unit := fun _ => ∅
  let systems : Nat -> Concept Nat Bool := targetAt
  have targetChanges (stage : Nat) :
      (parameters stage).target ≠ (parameters (stage + 1)).target := by
    intro equalTargets
    have equalAtCurrent := congrFun equalTargets stage
    simp [parameters, targetAt] at equalAtCurrent
  have reopensEveryStage (stage : Nat) :
      Reopens (parameters stage) (parameters (stage + 1))
        (languages stage) (languages (stage + 1)) (systems stage) := by
    constructor
    · exact Or.inr (Or.inl (targetChanges stage))
    · refine ⟨
        (⟨stage + 1, by simp [parameters]⟩,
          ⟨stage + 2, by simp [parameters]⟩), ?_, ?_⟩
      · simp [systems, targetAt]
      · simp [parameters, targetAt]
  refine ⟨parameters, languages, systems, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro stage
    simp [parameters]
  · intro stage
    exact Or.inr (Or.inl (targetChanges stage))
  · intro stage
    ext pair
    simp [parameters, systems, targetAt, defectRelation]
  · refine Filter.frequently_atTop.2 ?_
    intro lowerBound
    exact ⟨lowerBound, le_rfl, reopensEveryStage lowerBound⟩

/-- All definitions and the stagewise separation are exposed in one public
package, one conjunct per source formula or assertion. -/
theorem stopping_continuation_reopening :
    (∀ {X Coordinate Target : Type*}
      (readout : Concept X Coordinate) (target : Concept X Target),
      Closed readout target ↔ defectRelation readout target = ∅) ∧
    (∀ {X Coordinate Target Delta : Type*} [LE Delta]
      (deviation : Concept X Coordinate -> Concept X Target -> Delta)
      (readout : Concept X Coordinate) (target : Concept X Target)
      (precision : Delta),
      ApproximatelyClosed deviation readout target precision ↔
        deviation readout target ≤ precision) ∧
    (∀ {Decision Cost Gain Rate : Type*}
      [LE Cost] [HDiv Gain Cost Rate] [LE Rate]
      (cost : Decision -> Cost) (gain : Decision -> Gain)
      (budget : Cost) (threshold : Rate),
      BudgetStop cost gain budget threshold ↔
        ∀ decision, cost decision ≤ budget ->
          gain decision / cost decision ≤ threshold) ∧
    (∀ {Decision : Type*} (cost gain : Decision -> Real)
      (budget threshold : Real)
      (_feasibleNonempty :
        ({decision | cost decision ≤ budget} : Set Decision).Nonempty)
      (_ratiosBounded : BddAbove
        ((fun decision => gain decision / cost decision) ''
          {decision | cost decision ≤ budget})),
      BudgetStop cost gain budget threshold ↔
        sSup ((fun decision => gain decision / cost decision) ''
          {decision | cost decision ≤ budget}) ≤ threshold) ∧
    (∀ {System Evidence Proposal : Type*}
      (method : System -> Evidence -> Proposal)
      (system : System) (evidence : Evidence) (noProposal : Proposal),
      MethodStopped method system evidence noProposal ↔
        method system evidence = noProposal) ∧
    (∀ {World Coordinate Target Operation Precision : Type*}
      (parameters : LocalParameters World Target Operation Precision)
      (readout : Concept World Coordinate),
      LocallyComplete parameters readout ↔
        Closed
          (fun object : ↑parameters.objectDomain => readout object.1)
          (fun object : ↑parameters.objectDomain => parameters.target object.1)) ∧
    (∀ {World Target Operation Precision : Type*}
      (parameters : Nat -> LocalParameters World Target Operation Precision),
      OpenWorldSequence parameters ↔
        ∀ stage,
          LocalParametersChanged (parameters stage) (parameters (stage + 1))) ∧
    (∀ {World Coordinate Target Operation Precision Definition : Type*}
      (current next : LocalParameters World Target Operation Precision)
      (currentLanguage nextLanguage : Set Definition)
      (readout : Concept World Coordinate),
      Reopens current next currentLanguage nextLanguage readout ↔
        (current.objectDomain ≠ next.objectDomain ∨
          current.target ≠ next.target ∨
          current.precision ≠ next.precision ∨
          current.operationFamily ≠ next.operationFamily ∨
          currentLanguage ≠ nextLanguage) ∧
        (defectRelation
          (fun object : ↑next.objectDomain => readout object.1)
          (fun object : ↑next.objectDomain => next.target object.1)).Nonempty) ∧
    (∃ (parameters : Nat -> LocalParameters Nat Bool Unit Nat)
      (languages : Nat -> Set Unit)
      (systems : Nat -> Concept Nat Bool),
      Nonempty Bool ∧
        (∀ stage, (parameters stage).objectDomain.Nonempty) ∧
        OpenWorldSequence parameters ∧
        (∀ stage, LocallyComplete (parameters stage) (systems stage)) ∧
        (∃ᶠ stage in Filter.atTop,
          Reopens (parameters stage) (parameters (stage + 1))
            (languages stage) (languages (stage + 1)) (systems stage))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros
    rfl
  · intros
    rfl
  · intros
    rfl
  · intro Decision cost gain budget threshold _feasibleNonempty _ratiosBounded
    exact budget_stop_iff_sSup_le cost gain budget threshold
      _feasibleNonempty _ratiosBounded
  · intros
    rfl
  · intros
    rfl
  · intros
    rfl
  · intros
    rfl
  · exact stagewise_completion_with_infinite_reopening

/-- Positive finite control: the old fixed stage is genuinely complete, while
the changed target creates a nonempty canonical residual and reopens it. -/
example :
    let current : LocalParameters Bool Bool Unit Bool :=
      { objectDomain := Set.univ
        target := fun _ => false
        operationFamily := Set.univ
        precision := false }
    let next : LocalParameters Bool Bool Unit Bool :=
      { objectDomain := Set.univ
        target := id
        operationFamily := Set.univ
        precision := false }
    LocallyComplete current (fun _ => false) ∧
      Reopens current next (∅ : Set Unit) ∅ (fun _ => false) := by
  dsimp
  constructor
  · ext pair
    simp [defectRelation]
  · constructor
    · refine Or.inr (Or.inl ?_)
      intro equalTargets
      exact Bool.false_ne_true (congrFun equalTargets true)
    · exact ⟨(⟨false, Set.mem_univ false⟩, ⟨true, Set.mem_univ true⟩),
        rfl, Bool.false_ne_true⟩

/-- False-side finite control: changing precision alone is not a reopening when
the new canonical defect remains empty. This checks the required conjunction. -/
example :
    let current : LocalParameters Bool Bool Unit Bool :=
      { objectDomain := Set.univ
        target := id
        operationFamily := Set.univ
        precision := false }
    let next : LocalParameters Bool Bool Unit Bool :=
      { objectDomain := Set.univ
        target := id
        operationFamily := Set.univ
        precision := true }
    LocalParametersChanged current next ∧
      ¬Reopens current next (∅ : Set Unit) ∅ id := by
  dsimp
  constructor
  · exact Or.inr (Or.inr (Or.inr Bool.false_ne_true))
  · rintro ⟨_, ⟨⟨left, right⟩, sameReadout, differentTarget⟩⟩
    exact differentTarget sameReadout

#print axioms stopping_continuation_reopening

end D5.S3.ConceptDynamics.Termination.StoppingContinuationReopening
