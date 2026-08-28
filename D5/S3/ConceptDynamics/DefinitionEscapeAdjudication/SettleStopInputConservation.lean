/- GID: D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/SettleStopInputConservation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeAdjudication/SettleStopInputConservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Settlement stop is conserved by its decision and orientation inputs. -/

import D5.S3.ConceptDynamics.DefinitionEscapeAdjudication.AdjudicationStopTargetCorrectness

/- Library-search audit trail (2026-08-28):
   * `rg -n 'SettleStopInputConservation|settle_stop_depends_only_on_decision_and_orientation|
     settleStop|AdjudicationStopTarget|decision.*orientation|orientation.*decision'
     D5 --glob '*.lean'` found the frozen `settleStop` definition and its exact
     checker theorem, but no conservation theorem for equal sealed decisions.
   * The same exact-name and statement-shape search in pinned Mathlib found no
     hit. This result is repository-specific congruence for the canonical
     `ProspectiveCommitment` projection, so no third-party dependency is needed.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

open D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion

universe u

/-- The settlement stop component consumes only the commitment's sealed
decision set and the supplied sourced orientation. -/
theorem settle_stop_depends_only_on_decision_and_orientation
    {Goal Source Version Scope EventId Evidence Round Action Time TargetChain
      Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Action]
    (AdmTarget : Goal -> Set Action)
    (InScope : Scope -> Action -> Prop)
    (O O' : OrientationSpec Goal Action Source Version Scope AdmTarget InScope)
    {n : Round}
    (K K' : ProspectiveCommitment EventId Evidence Round Action Time TargetChain
      Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
    [admissibleDecidable : forall a, Decidable (a ∈ AdmTarget O.goal)]
    [scopeDecidable : forall a, Decidable (InScope O.scope a)]
    [relationDecidable : forall a b, Decidable (O.relation a b)]
    [admissibleDecidable' : forall a, Decidable (a ∈ AdmTarget O'.goal)]
    [scopeDecidable' : forall a, Decidable (InScope O'.scope a)]
    [relationDecidable' : forall a b, Decidable (O'.relation a b)]
    (equalInputs : K.decision = K'.decision ∧ O = O') :
    settleStop AdmTarget InScope O K =
      settleStop AdmTarget InScope O' K' := by
  rcases equalInputs with ⟨decisionEqual, orientationEqual⟩
  subst O'
  have admissibleInstancesEqual :
      admissibleDecidable = admissibleDecidable' := Subsingleton.elim _ _
  have scopeInstancesEqual :
      scopeDecidable = scopeDecidable' := Subsingleton.elim _ _
  have relationInstancesEqual :
      relationDecidable = relationDecidable' := Subsingleton.elim _ _
  subst admissibleDecidable'
  subst scopeDecidable'
  subst relationDecidable'
  simp only [settleStop]
  rw [decisionEqual]

/- The repository's finite commitment witness and an equality orientation
   jointly witness the theorem's domain and all of its hypotheses. -/
example :
    let AdmTarget : Unit -> Set Bool := fun _ => Set.univ
    let InScope : Unit -> Bool -> Prop := fun _ _ => True
    let O : OrientationSpec Unit Bool Unit Unit Unit AdmTarget InScope :=
      { goal := ()
        relation := Eq
        source := ()
        version := ()
        scope := ()
        relationInDeclaredDomain := by
          intro a b _
          exact ⟨Set.mem_univ a, Set.mem_univ b, True.intro, True.intro⟩
        refl := by
          intro _ _ _
          exact rfl
        trans := by
          intro _ _ _ _ _ _ _ _ _ hab hbc
          exact hab.trans hbc }
    settleStop AdmTarget InScope O FiniteWitness.oldK =
      settleStop AdmTarget InScope O FiniteWitness.unchangedK := by
  dsimp
  apply settle_stop_depends_only_on_decision_and_orientation
  exact ⟨rfl, rfl⟩

example : FiniteWitness.Commitment := FiniteWitness.oldK

#print axioms settle_stop_depends_only_on_decision_and_orientation

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
