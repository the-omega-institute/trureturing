/- GID: D5/S3/ConceptDynamics/DefinitionEscapeLaws/ScientificGainGeneralizationReversal
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeLaws/ScientificGainGeneralizationReversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exhibit equal observed marginals with opposite conditional future loss signs. -/

import D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion
import D5.S3.Divergence.ChainRule

/- Library-search audit trail (2026-08-30):
   * `rg -n -i 'same observed marginal|identical observed marginal|opposite.*conditional.*expect|
     conditional.*expect.*opposite|scientific gain.*generalization|generalization.*scientific gain|
     future loss.*sign|sign reversal' D5 --glob '*.lean'` found no existing
     scientific-gain/generalization reversal; its only hits were unrelated sign reversals.
   * `rg -n 'ScientificGain|Loss_K|nextEvidence|NonAnticipating.*evaluate|
     marginal.*conditional' D5 --glob '*.lean'` found no frozen `ScientificGain` declaration.
     It did find the canonical finite `marginal` and `conditional` operations in
     `D5.S3.Divergence.ChainRule`, which are imported and reused below.
   * `rg -n -i 'same.*marginal|identical.*marginal|opposite.*expect|
     conditional.*sign|sign.*conditional' .lake/packages/mathlib/Mathlib --glob '*.lean'`
     returned no hits. Pinned Mathlib supplies the finite sums and real arithmetic only.
   * The source's definitional `NonAnticipating` and `ScientificGain` skeletons are
     transcribed over the frozen `AdjudicationSnapshot` and `ProspectiveCommitment`
     carriers. The theorem is not obtained by unfolding either definition: it also
     verifies two probability laws, their common observed marginal, integrability,
     and two independently computed conditional expectations with opposite signs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

noncomputable section

namespace D5.S3.ConceptDynamics.DefinitionEscapeLaws.ScientificGainGeneralizationReversal

open D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion
open D5.S3.Divergence.ChainRule

universe u v

/-- The source's adjudication-level non-anticipation predicate. -/
def NonAnticipating
    {EventId Evidence Round Artifact Time : Type u}
    [Preorder EventId] [Preorder Time] {n : Round}
    (K : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (z : Evidence) : Prop :=
  z ∈ K.filtration.seen K.decisionEvent ∧
    z ∉ K.filtration.seen K.freezeEvent ∧
    z ∉ K.evidenceDependencies

/-- The source's one-record prospective scientific-gain predicate. -/
def ScientificGain
    {EventId Evidence Round Action Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec : Type u}
    {Loss : Type v} [LT Loss]
    [LinearOrder EventId] [Preorder Time] [DecidableEq Action]
    {n : Round}
    (evaluate : Comparator -> Action -> Evidence -> Loss)
    (K : ProspectiveCommitment EventId Evidence Round Action Time TargetChain
      Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
    (z : Evidence) (a b : Action) : Prop :=
  a ∈ K.committedArtifacts ∧
    b ∈ K.baselineArtifacts ∧
    NonAnticipating K.adjudication z ∧
    evaluate K.comparator a z < evaluate K.comparator b z

/-- A real-valued finite joint law has mass in the unit interval and total mass one. -/
def IsFiniteJointLaw
    {Observed Next : Type*} [Fintype Observed] [Fintype Next]
    (law : Observed × Next -> Real) : Prop :=
  (forall point, 0 <= law point ∧ law point <= 1) ∧
    ∑ point, law point = 1

/-- The source loss is uniquely the frozen evaluator at the next evidence record. -/
def prospectiveLoss
    {Comparator Action Evidence Next : Type*}
    (evaluate : Comparator -> Action -> Evidence -> Real)
    (comparator : Comparator) (nextEvidence : Next -> Evidence)
    (action : Action) (next : Next) : Real :=
  evaluate comparator action (nextEvidence next)

/-- The loss difference is derived from the same evaluator and comparator. -/
def lossDifference
    {Comparator Action Evidence Next : Type*}
    (evaluate : Comparator -> Action -> Evidence -> Real)
    (comparator : Comparator) (nextEvidence : Next -> Evidence)
    (a b : Action) (next : Next) : Real :=
  prospectiveLoss evaluate comparator nextEvidence a next -
    prospectiveLoss evaluate comparator nextEvidence b next

/-- Absolute integrability is checked explicitly as absolute summability of the
finite joint-law-weighted source loss. -/
def AbsolutelyIntegrableLoss
    {Observed Next Comparator Action Evidence : Type*}
    (law : Observed × Next -> Real)
    (evaluate : Comparator -> Action -> Evidence -> Real)
    (comparator : Comparator) (nextEvidence : Next -> Evidence)
    (action : Action) : Prop :=
  Summable fun point : Observed × Next =>
    |law point * prospectiveLoss evaluate comparator nextEvidence action point.2|

/-- Conditional expected loss difference, using the repository's canonical
finite conditional law. -/
noncomputable def conditionalExpectedLossDifference
    {Observed Next Comparator Action Evidence : Type*} [Fintype Next]
    (law : Observed × Next -> Real) (history : Observed)
    (evaluate : Comparator -> Action -> Evidence -> Real)
    (comparator : Comparator) (nextEvidence : Next -> Evidence)
    (a b : Action) : Real :=
  ∑ next, conditional law history next *
    lossDifference evaluate comparator nextEvidence a b next

/-- The finite witness uses the frozen prospective-commitment carrier. -/
abbrev WitnessCommitment :=
  ProspectiveCommitment Bool Bool Unit Bool Unit Unit Unit Unit Unit Unit Unit Unit Unit ()

/-- Freeze sees no evidence and decision sees every evidence record. -/
def witnessFiltration : EvidenceFiltration Bool Bool where
  seen event := if event then Set.univ else ∅
  monotone := by
    intro i j hij z hz
    cases i <;> cases j <;> simp [Bool.le_iff_imp] at hij hz ⊢

/-- A concrete valid adjudication snapshot for the scientific-gain premise. -/
def witnessAdjudication : AdjudicationSnapshot Bool Bool Unit Bool Unit () where
  freezeEvent := false
  decisionEvent := true
  frozenAt := ()
  decidedAt := ()
  freezeBeforeDecision := by decide
  timeBeforeDecision := le_rfl
  filtration := witnessFiltration
  dependencyClosure := Set.univ
  evidenceDependencies := ∅

/-- Both Boolean actions are candidates and feasible, with `false` current. -/
def witnessDecision : DecisionSet Bool where
  candidates := Finset.univ
  feasible := Finset.univ
  current := some false
  feasibleFromCandidates := Finset.Subset.rfl

/-- Action `false` is committed and action `true` is its preregistered baseline. -/
def witnessCommitment : WitnessCommitment where
  adjudication := witnessAdjudication
  targetChain := ()
  domain := ()
  epsilon := ()
  conditions := ()
  comparator := ()
  testPlan := ()
  baseline := ()
  weightSpec := ()
  decision := witnessDecision
  committedArtifacts := {false}
  baselineArtifacts := {true}
  committedFromCandidates := by simp [witnessDecision]
  baselinesFromCandidates := by simp [witnessDecision]
  committedInClosure := by simp [witnessAdjudication]

/-- On the historical `false` record the committed action has lower loss;
on the possible `true` next record the ranking reverses. -/
def witnessEvaluate : Unit -> Bool -> Bool -> Real := fun _ action evidence =>
  if evidence then
    if action then 0 else 1
  else
    if action then 1 else 0

/-- The first joint law concentrates its future record on `false`. -/
def witnessP : Unit × Bool -> Real := fun point =>
  if point.2 then 0 else 1

/-- The second joint law has the same observed marginal but concentrates its
future record on `true`. -/
def witnessQ : Unit × Bool -> Real := fun point =>
  if point.2 then 1 else 0

/-- Equal complete observed marginals and a positive shared history do not let
one scientific-gain observation identify the sign of future conditional loss:
the same frozen evaluator yields conditional differences `-1` and `+1`. -/
theorem scientific_gain_generalization_sign_reversal :
    exists (P Q : Unit × Bool -> Real)
      (nextEvidence : Bool -> Bool) (lastEvidence : Unit -> Bool)
      (evaluate : Unit -> Bool -> Bool -> Real)
      (K : WitnessCommitment) (hStar : Unit) (zStar a b : Bool),
      IsFiniteJointLaw P ∧
      IsFiniteJointLaw Q ∧
      (forall h, marginal P h = marginal Q h) ∧
      marginal P hStar = marginal Q hStar ∧
      0 < marginal P hStar ∧
      lastEvidence hStar = zStar ∧
      ScientificGain evaluate K zStar a b ∧
      (forall action,
        AbsolutelyIntegrableLoss P evaluate K.comparator nextEvidence action ∧
        AbsolutelyIntegrableLoss Q evaluate K.comparator nextEvidence action) ∧
      conditionalExpectedLossDifference P hStar evaluate K.comparator
          nextEvidence a b < 0 ∧
      0 < conditionalExpectedLossDifference Q hStar evaluate K.comparator
          nextEvidence a b := by
  refine ⟨witnessP, witnessQ, id, fun _ => false, witnessEvaluate,
    witnessCommitment, (), false, false, true, ?_⟩
  constructor
  · constructor
    · intro point
      cases point with
      | mk history next =>
          cases history
          cases next <;> simp [witnessP]
    · rw [Fintype.sum_prod_type]
      simp [witnessP]
  constructor
  · constructor
    · intro point
      cases point with
      | mk history next =>
          cases history
          cases next <;> simp [witnessQ]
    · rw [Fintype.sum_prod_type]
      simp [witnessQ]
  constructor
  · intro history
    cases history
    simp [marginal, witnessP, witnessQ]
  constructor
  · simp [marginal, witnessP, witnessQ]
  constructor
  · simp [marginal, witnessP]
  constructor
  · rfl
  constructor
  · simp [ScientificGain, NonAnticipating, witnessCommitment,
      witnessAdjudication, witnessFiltration, witnessEvaluate]
  constructor
  · intro action
    exact ⟨Summable.of_finite, Summable.of_finite⟩
  constructor <;>
    simp [conditionalExpectedLossDifference, conditional, marginal,
      lossDifference, prospectiveLoss, witnessP, witnessQ, witnessEvaluate]

/-- The witness domain is inhabited independently of the theorem proof. -/
example : WitnessCommitment := witnessCommitment

#print axioms scientific_gain_generalization_sign_reversal

end D5.S3.ConceptDynamics.DefinitionEscapeLaws.ScientificGainGeneralizationReversal
