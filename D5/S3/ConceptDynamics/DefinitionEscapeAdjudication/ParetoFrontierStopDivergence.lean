/- GID: D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoFrontierStopDivergence
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoFrontierStopDivergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One Pareto frontier yields opposite stops under two sourced orientations. -/

import D5.S3.ConceptDynamics.DefinitionEscapeAdjudication.ParetoWeakPreorder
import D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/- Library-search audit trail (2026-08-28):
   * `rg -n "NoDominatingCandidate|AdjudicationStopTargetOnDecisionSet|
     OrientationSpec|pareto_frontier.*stop|finite.*stop.*orientation|different.*stop"
     D5 --glob '*.lean'` found no existing stop target, sourced orientation, or
     theorem with the atom's positive/negative finite certificate shape.
   * `rg -n -i "NoDominatingCandidate|OrientationSpec|ParetoWeak|ParetoStrict|
     AdjudicationStop|stopCheck" .lake/packages/mathlib/Mathlib --glob '*.lean'`
     found no names. Shape searches found only generic finite maximal-element
     results and the unrelated Pareto probability distribution.
   * `gh search code '<name> language:Lean' --limit 20`, run separately for
     `NoDominatingCandidate`, `OrientationSpec`, and `ParetoWeak`, returned no
     third-party Lean code hits.
   * The frozen `ParetoWeakPreorder` supplies the atom's five-coordinate weak
     dominance unchanged. The frozen governance commitment module supplies the
     canonical `DecisionSet`, reused through the abbreviation below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

universe u

/-- The source decision carrier, reused from the canonical governance module. -/
abbrev DecisionSet (Action : Type u) [DecidableEq Action] :=
  D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion.DecisionSet Action

/-- A sourced and scoped preorder used to orient an adjudication decision. -/
structure OrientationSpec
    (Goal Action Source Version Scope : Type u)
    (AdmTarget : Goal -> Set Action)
    (InScope : Scope -> Action -> Prop) where
  goal : Goal
  relation : Action -> Action -> Prop
  source : Source
  version : Version
  scope : Scope
  relationInDeclaredDomain : forall {a b}, relation a b ->
    a ∈ AdmTarget goal ∧ b ∈ AdmTarget goal ∧
      InScope scope a ∧ InScope scope b
  refl : forall a, a ∈ AdmTarget goal -> InScope scope a -> relation a a
  trans : forall {a b c},
    a ∈ AdmTarget goal -> b ∈ AdmTarget goal -> c ∈ AdmTarget goal ->
    InScope scope a -> InScope scope b -> InScope scope c ->
    relation a b -> relation b c -> relation a c

/-- Strict Pareto dominance is weak dominance without its reverse. -/
def ParetoStrict
    {Action Information Residual Transfer Cost Risk : Type u}
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    (value : Action -> GainVector Information Residual Transfer Cost Risk)
    (a b : Action) : Prop :=
  ParetoWeak value a b ∧ ¬ ParetoWeak value b a

/-- The current candidate has no strict Pareto dominator among the candidates. -/
def NoDominatingCandidate
    {Action Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    (value : Action -> GainVector Information Residual Transfer Cost Risk)
    (D : DecisionSet Action) : Prop :=
  ∃ current, D.current = some current ∧
    current ∈ D.candidates ∧
    ¬ ∃ a, a ∈ D.candidates ∧ ParetoStrict value a current

/-- The named stop target consumes only the decision set and a complete
sourced orientation on its declared target and scope. -/
def AdjudicationStopTargetOnDecisionSet
    {Goal Action Source Version Scope : Type u}
    [DecidableEq Action]
    (AdmTarget : Goal -> Set Action)
    (InScope : Scope -> Action -> Prop)
    (O : OrientationSpec Goal Action Source Version Scope AdmTarget InScope)
    (D : DecisionSet Action) : Prop :=
  ∃ current, D.current = some current ∧ current ∈ D.feasible ∧
    (forall a, a ∈ D.feasible ->
      a ∈ AdmTarget O.goal ∧ InScope O.scope a) ∧
    ¬ ∃ a, a ∈ D.feasible ∧ O.relation current a ∧
      ¬ O.relation a current

/-- The two-action carrier from obligation 56.3-B. -/
abbrev ActionTwo := Fin 2

/-- Candidates and feasible actions coincide, and action zero is current. -/
def decisionTwo : DecisionSet ActionTwo where
  candidates := Finset.univ
  feasible := Finset.univ
  current := some 0
  feasibleFromCandidates := by
    intro action membership
    exact membership

/-- Actions zero and one each have a strict advantage in one benefit
coordinate; their remaining coordinates agree. -/
def valueTwo : ActionTwo -> GainVector Nat Nat Nat Nat Nat := fun action =>
  if action = 0 then
    { information := 1
      residualCapture := 0
      transfer := 0
      lifecycleCost := 0
      risk := 0 }
  else
    { information := 0
      residualCapture := 1
      transfer := 0
      lifecycleCost := 0
      risk := 0 }

/-- Every action belongs to the single goal's admissible target. -/
def admissibleTargetTwo : Unit -> Set ActionTwo := fun _ => Set.univ

/-- Every action is inside the single declared scope. -/
def inScopeTwo : Unit -> ActionTwo -> Prop := fun _ _ => True

/-- Equality orientation records the false source and version. -/
def stayOrientation : OrientationSpec Unit ActionTwo Bool Bool Unit
    admissibleTargetTwo inScopeTwo where
  goal := ()
  relation := Eq
  source := false
  version := false
  scope := ()
  relationInDeclaredDomain := by
    intro a b _
    exact ⟨Set.mem_univ a, Set.mem_univ b, True.intro, True.intro⟩
  refl := by
    intro a _ _
    exact rfl
  trans := by
    intro a b c _ _ _ _ _ _ hab hbc
    exact hab.trans hbc

/-- Natural index order records the true source and version. -/
def advanceOrientation : OrientationSpec Unit ActionTwo Bool Bool Unit
    admissibleTargetTwo inScopeTwo where
  goal := ()
  relation := fun a b => a.1 <= b.1
  source := true
  version := true
  scope := ()
  relationInDeclaredDomain := by
    intro a b _
    exact ⟨Set.mem_univ a, Set.mem_univ b, True.intro, True.intro⟩
  refl := by
    intro _ _ _
    exact le_rfl
  trans := by
    intro _ _ _ _ _ _ _ _ _ hab hbc
    exact le_trans hab hbc

/-- One nonempty decision set has no strict Pareto dominator and stops under
the equality orientation, but it does not stop under index order. Hence its
Pareto frontier alone cannot imply the sourced advance-oriented stop. -/
theorem pareto_frontier_requires_sourced_orientation :
    (NoDominatingCandidate valueTwo decisionTwo ∧
      AdjudicationStopTargetOnDecisionSet
        admissibleTargetTwo inScopeTwo stayOrientation decisionTwo ∧
      ¬ AdjudicationStopTargetOnDecisionSet
        admissibleTargetTwo inScopeTwo advanceOrientation decisionTwo) ∧
    ¬ (NoDominatingCandidate valueTwo decisionTwo ->
      AdjudicationStopTargetOnDecisionSet
        admissibleTargetTwo inScopeTwo advanceOrientation decisionTwo) := by
  have noDominator : NoDominatingCandidate valueTwo decisionTwo := by
    refine ⟨0, rfl, by simp [decisionTwo], ?_⟩
    rintro ⟨action, _, strictDominance⟩
    fin_cases action <;>
      simp [ParetoStrict, ParetoWeak, valueTwo] at strictDominance
  have stayStop : AdjudicationStopTargetOnDecisionSet
      admissibleTargetTwo inScopeTwo stayOrientation decisionTwo := by
    refine ⟨0, rfl, by simp [decisionTwo], ?_, ?_⟩
    · intro action _
      exact ⟨Set.mem_univ action, True.intro⟩
    · rintro ⟨action, _, forward, notReverse⟩
      exact notReverse forward.symm
  have notAdvanceStop : ¬ AdjudicationStopTargetOnDecisionSet
      admissibleTargetTwo inScopeTwo advanceOrientation decisionTwo := by
    rintro ⟨current, currentValue, _, _, noAdvance⟩
    change some (0 : ActionTwo) = some current at currentValue
    have currentIsZero : (0 : ActionTwo) = current := Option.some.inj currentValue
    subst current
    apply noAdvance
    refine ⟨1, by simp [decisionTwo], ?_, ?_⟩
    · change (0 : Nat) <= 1
      exact Nat.zero_le 1
    · change ¬(1 : Nat) <= 0
      exact Nat.not_succ_le_zero 0
  exact
    ⟨⟨noDominator, stayStop, notAdvanceStop⟩,
      fun implication => notAdvanceStop (implication noDominator)⟩

/-- The concrete action domain used by the certificate is inhabited. -/
example : ActionTwo := 0

#print axioms pareto_frontier_requires_sourced_orientation

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
