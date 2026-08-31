/- GID: D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoLinearExtensionStopRefutation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoLinearExtensionStopRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A sourced two-action Pareto model refutes both OP5 linear-extension stop equivalences. -/

import D5.S3.ConceptDynamics.DefinitionEscapeAdjudication.AdjudicationStopTargetCorrectness
import D5.S3.ConceptDynamics.DefinitionEscapeAdjudication.QuotientParetoWeakOrder
import Mathlib.Order.Extension.Linear

/- Library-search audit trail (2026-08-31):
   * Exact D5 searches for `ParetoLinearExtensionStopRefutation`,
     `op5_pareto_stop_linear_extension_equivalences_refuted`, `Pareto-maximal`,
     `Pareto-greatest`, and Pareto linear-extension stop equivalences found no
     existing declaration. Shape searches found the frozen finite Pareto
     quotient/order and oriented-stop modules imported above, but no OP5 model.
   * Pinned Mathlib's `extend_partialOrder` is the Szpilrajn extension theorem.
     No pinned theorem combines a maximal or greatest element with the
     repository's sourced `OrientationSpec` or `OrientedStop` predicate.
   * GitHub Lean-code searches for `Pareto maximal linear extension`,
     `extend_partialOrder maximal`, and `LinearExtension maximal` returned no
     third-party code hits. Local `loogle` and `leansearch` executables were absent.
   * The countermodel uses the frozen convention that `ParetoWeak value a b`
     means `a` dominates `b`. Extending that relation as a less-than-or-equal
     order makes the dominating action a strict predecessor, while the frozen
     stop predicate rejects strict successors of the current action. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

open D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion

universe u

/-- The source's finite scope narrowing: the original scope is retained in the
first coordinate and membership in the finite feasible set is added explicitly. -/
def InFiniteNarrowedScope
    {Scope Action : Type u}
    (InScope : Scope -> Action -> Prop) :
    (Scope × Finset Action) -> Action -> Prop :=
  fun scopeAndCarrier action =>
    InScope scopeAndCarrier.1 action ∧ action ∈ scopeAndCarrier.2

/-- The explicit quotient class containing a member of the finite carrier. -/
def finiteParetoClassOf
    {Action Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [Preorder Information] [Preorder Residual] [Preorder Transfer]
    [Preorder Cost] [Preorder Risk]
    [DecidableRel ((· ≤ ·) : Information -> Information -> Prop)]
    [DecidableRel ((· ≤ ·) : Residual -> Residual -> Prop)]
    [DecidableRel ((· ≤ ·) : Transfer -> Transfer -> Prop)]
    [DecidableRel ((· ≤ ·) : Cost -> Cost -> Prop)]
    [DecidableRel ((· ≤ ·) : Risk -> Risk -> Prop)]
    (value : Action -> GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (x : ParetoCarrier F) :
    FiniteParetoQuotient value F :=
  ⟨paretoClass value F x,
    Finset.mem_image_of_mem (paretoClass value F) (mem_carrierEnum F x)⟩

/-- A member of `LinExt_F(O_P)` is a complete quotient linear extension together
with the full sourced, versioned, and finitely narrowed orientation pulled back
to the action carrier. It is not a bare binary relation. -/
structure SourcedParetoLinearExtension
    {Goal Action Source Version Scope Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [Preorder Information] [Preorder Residual] [Preorder Transfer]
    [Preorder Cost] [Preorder Risk]
    [DecidableRel ((· ≤ ·) : Information -> Information -> Prop)]
    [DecidableRel ((· ≤ ·) : Residual -> Residual -> Prop)]
    [DecidableRel ((· ≤ ·) : Transfer -> Transfer -> Prop)]
    [DecidableRel ((· ≤ ·) : Cost -> Cost -> Prop)]
    [DecidableRel ((· ≤ ·) : Risk -> Risk -> Prop)]
    (AdmTarget : Goal -> Set Action)
    (InScope : Scope -> Action -> Prop)
    (paretoOrientation : OrientationSpec Goal Action Source Version Scope
      AdmTarget InScope)
    (value : Action -> GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) where
  quotientRelation :
    FiniteParetoQuotient value F -> FiniteParetoQuotient value F -> Prop
  quotientLinearOrder :
    IsLinearOrder (FiniteParetoQuotient value F) quotientRelation
  extendsQuotientPareto : forall C D,
    QuotientParetoWeak value F C D -> quotientRelation C D
  orientation : OrientationSpec Goal Action Source Version
    (Scope × Finset Action) AdmTarget (InFiniteNarrowedScope InScope)
  baseRelation : forall a b,
    paretoOrientation.relation a b <-> ParetoWeak value a b
  preservesGoal : orientation.goal = paretoOrientation.goal
  preservesSource : orientation.source = paretoOrientation.source
  preservesVersion : orientation.version = paretoOrientation.version
  narrowsScope : orientation.scope = (paretoOrientation.scope, F)
  relation_iff : forall a b,
    orientation.relation a b <->
      ∃ (ha : a ∈ F) (hb : b ∈ F),
        quotientRelation
          (finiteParetoClassOf value F ⟨a, ha⟩)
          (finiteParetoClassOf value F ⟨b, hb⟩)

/-- Conventional Pareto maximality on the finite feasible set: the current
action is feasible and no other feasible action strictly dominates it. -/
def ParetoMaximalIn
    {Action Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    (value : Action -> GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (current : Action) : Prop :=
  current ∈ F ∧
    ¬ ∃ action, action ∈ F ∧ ParetoStrict value action current

/-- Pareto greatestness on the finite feasible set: the current action weakly
dominates every feasible action. -/
def ParetoGreatestIn
    {Action Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    (value : Action -> GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (current : Action) : Prop :=
  current ∈ F ∧ ∀ action, action ∈ F -> ParetoWeak value current action

namespace OP5Countermodel

/-- The nonempty two-action feasible set. -/
def feasible : Finset Bool := Finset.univ

/-- `true` strictly dominates `false` in every one of the five public
coordinates. -/
def value : Bool -> GainVector Nat Nat Nat Nat Nat := fun action =>
  if action then
    { information := 1
      residualCapture := 1
      transfer := 1
      lifecycleCost := 0
      risk := 0 }
  else
    { information := 0
      residualCapture := 0
      transfer := 0
      lifecycleCost := 1
      risk := 1 }

/-- Both actions are admissible. -/
def admissibleTarget : Unit -> Set Bool := fun _ => Set.univ

/-- Both actions lie in the original declared scope. -/
def inScope : Unit -> Bool -> Prop := fun _ _ => True

/-- The complete Pareto orientation records a nontrivial source and version. -/
def paretoOrientation : OrientationSpec Unit Bool Bool Bool Unit
    admissibleTarget inScope where
  goal := ()
  relation := ParetoWeak value
  source := true
  version := false
  scope := ()
  relationInDeclaredDomain := by
    intro a b _
    exact ⟨Set.mem_univ a, Set.mem_univ b, True.intro, True.intro⟩
  refl := by
    intro action _ _
    exact (pareto_weak_reflexive_transitive value).1 action
  trans := by
    intro a b c _ _ _ _ _ _ hab hbc
    exact (pareto_weak_reflexive_transitive value).2 hab hbc

/-- The commitment's sealed decision has feasible set `feasible` and current
action `true`. -/
def decision : DecisionSet Bool where
  candidates := feasible
  feasible := feasible
  current := some true
  feasibleFromCandidates := by intro action membership; exact membership

/-- A complete same-round commitment carrying the countermodel decision. -/
def commitment :
    ProspectiveCommitment
      (Fin 2) Bool Bool Bool (Fin 3) Unit Unit Unit Bool Unit Unit Unit Unit false where
  adjudication := FiniteWitness.seenSnapshot
  targetChain := ()
  domain := ()
  epsilon := ()
  conditions := false
  comparator := ()
  testPlan := ()
  baseline := ()
  weightSpec := ()
  decision := decision
  committedArtifacts := ∅
  baselineArtifacts := ∅
  committedFromCandidates := by simp
  baselinesFromCandidates := by simp
  committedInClosure := by simp

abbrev Quotient := FiniteParetoQuotient value feasible

abbrev LinearExtension :=
  SourcedParetoLinearExtension admissibleTarget inScope paretoOrientation
    value feasible

instance quotientPartialOrder :
    IsPartialOrder Quotient (QuotientParetoWeak value feasible) where
  refl := quotientParetoWeak_refl value feasible
  trans := fun C D E => quotientParetoWeak_trans value feasible C D E
  antisymm := fun C D => quotientParetoWeak_antisymm value feasible C D

/-- A Szpilrajn linear extension of the frozen quotient Pareto order. -/
noncomputable def extensionRelation : Quotient -> Quotient -> Prop :=
  (extend_partialOrder (QuotientParetoWeak value feasible)).choose

theorem extensionRelation_linear :
    IsLinearOrder Quotient extensionRelation :=
  (extend_partialOrder (QuotientParetoWeak value feasible)).choose_spec.1

theorem extensionRelation_extends : forall C D,
    QuotientParetoWeak value feasible C D -> extensionRelation C D :=
  (extend_partialOrder (QuotientParetoWeak value feasible)).choose_spec.2

/-- The chosen quotient extension pulled back to the full action carrier. -/
noncomputable def extensionOrientation : OrientationSpec Unit Bool Bool Bool
    (Unit × Finset Bool) admissibleTarget (InFiniteNarrowedScope inScope) where
  goal := paretoOrientation.goal
  relation := fun a b =>
    ∃ (ha : a ∈ feasible) (hb : b ∈ feasible),
      extensionRelation
        (finiteParetoClassOf value feasible ⟨a, ha⟩)
        (finiteParetoClassOf value feasible ⟨b, hb⟩)
  source := paretoOrientation.source
  version := paretoOrientation.version
  scope := (paretoOrientation.scope, feasible)
  relationInDeclaredDomain := by
    rintro a b ⟨ha, hb, _⟩
    exact
      ⟨Set.mem_univ a, Set.mem_univ b,
        ⟨True.intro, ha⟩, ⟨True.intro, hb⟩⟩
  refl := by
    intro action _ narrowed
    exact ⟨narrowed.2, narrowed.2, extensionRelation_linear.refl _⟩
  trans := by
    rintro a b c _ _ _ _ _ _ ⟨ha, hb, hab⟩ ⟨hb', hc, hbc⟩
    refine ⟨ha, hc, ?_⟩
    simpa using extensionRelation_linear.trans
      (finiteParetoClassOf value feasible ⟨a, ha⟩)
      (finiteParetoClassOf value feasible ⟨b, hb⟩)
      (finiteParetoClassOf value feasible ⟨c, hc⟩)
      hab (by simpa using hbc)

/-- The complete sourced linear extension used to witness nonemptiness of
`LinExt_F(O_P)`. -/
noncomputable def linearExtension : LinearExtension where
  quotientRelation := extensionRelation
  quotientLinearOrder := extensionRelation_linear
  extendsQuotientPareto := extensionRelation_extends
  orientation := extensionOrientation
  baseRelation := by intro _ _; rfl
  preservesGoal := rfl
  preservesSource := rfl
  preservesVersion := rfl
  narrowsScope := rfl
  relation_iff := by intro _ _; rfl

theorem trueClass_ne_falseClass :
    finiteParetoClassOf value feasible ⟨true, by simp [feasible]⟩ ≠
      finiteParetoClassOf value feasible ⟨false, by simp [feasible]⟩ := by
  intro classesEqual
  have classValuesEqual := congrArg Subtype.val classesEqual
  have equivalent :=
    (paretoClass_eq_iff value feasible
      ⟨true, by simp [feasible]⟩ ⟨false, by simp [feasible]⟩).1 classValuesEqual
  simp [ParetoEqOn, ParetoWeakOn, ParetoWeak, value] at equivalent

/-- Every complete quotient linear extension puts the dominating action before
the dominated action, so the frozen successor-rejecting stop predicate cannot
stop at the dominating current action. -/
theorem no_linear_extension_stops_at_true (L : LinearExtension) :
    ¬ OrientedStop admissibleTarget (InFiniteNarrowedScope inScope)
      L.orientation commitment := by
  let trueCarrier : ParetoCarrier feasible := ⟨true, by simp [feasible]⟩
  let falseCarrier : ParetoCarrier feasible := ⟨false, by simp [feasible]⟩
  let trueClass := finiteParetoClassOf value feasible trueCarrier
  let falseClass := finiteParetoClassOf value feasible falseCarrier
  have quotientForward : QuotientParetoWeak value feasible trueClass falseClass := by
    refine
      ⟨trueCarrier, mem_paretoClass_self value feasible trueCarrier,
        falseCarrier, mem_paretoClass_self value feasible falseCarrier, ?_⟩
    simp [ParetoWeakOn, ParetoWeak, value, trueCarrier, falseCarrier]
  have linearForward : L.quotientRelation trueClass falseClass :=
    L.extendsQuotientPareto trueClass falseClass quotientForward
  have notLinearReverse : ¬ L.quotientRelation falseClass trueClass := by
    intro linearReverse
    have classesEqual :=
      L.quotientLinearOrder.antisymm trueClass falseClass
        linearForward linearReverse
    exact trueClass_ne_falseClass (by simpa [trueClass, falseClass] using classesEqual)
  have orientationForward : L.orientation.relation true false := by
    apply (L.relation_iff true false).2
    refine ⟨by simp [feasible], by simp [feasible], ?_⟩
    simpa [trueClass, falseClass, trueCarrier, falseCarrier] using linearForward
  have notOrientationReverse : ¬ L.orientation.relation false true := by
    intro orientationReverse
    rcases (L.relation_iff false true).1 orientationReverse with
      ⟨falseMem, trueMem, linearReverse⟩
    apply notLinearReverse
    simpa [trueClass, falseClass, trueCarrier, falseCarrier] using linearReverse
  rintro ⟨current, currentValue, _, _, noSuccessor⟩
  have currentIsTrue : current = true := by
    change some true = some current at currentValue
    exact (Option.some.inj currentValue).symm
  subst current
  apply noSuccessor
  exact
    ⟨false, by simp [commitment, decision, feasible],
      orientationForward, notOrientationReverse⟩

theorem true_pareto_maximal : ParetoMaximalIn value feasible true := by
  refine ⟨by simp [feasible], ?_⟩
  rintro ⟨action, _, strictDominance⟩
  cases action <;>
    simp [ParetoStrict, ParetoWeak, value] at strictDominance

theorem true_pareto_greatest : ParetoGreatestIn value feasible true := by
  refine ⟨by simp [feasible], ?_⟩
  intro action _
  cases action <;> simp [ParetoWeak, value]

end OP5Countermodel

open OP5Countermodel

/-- OP5 is false as written. In this complete finite model `true` is both
Pareto-maximal and Pareto-greatest, at least one fully sourced quotient linear
extension exists, and no such extension produces `OrientedStop`. Consequently
both the existential/maximal and universal/greatest equivalences are refuted. -/
theorem op5_pareto_stop_linear_extension_equivalences_refuted :
    (feasible.Nonempty ∧
      commitment.decision.feasible = feasible ∧
      commitment.decision.current = some true ∧
      (∀ action, action ∈ feasible ->
        action ∈ admissibleTarget paretoOrientation.goal ∧
          inScope paretoOrientation.scope action) ∧
      ParetoMaximalIn value feasible true ∧
      ParetoGreatestIn value feasible true ∧
      Nonempty LinearExtension) ∧
    ¬ (ParetoMaximalIn value feasible true <->
      ∃ L : LinearExtension,
        OrientedStop admissibleTarget (InFiniteNarrowedScope inScope)
          L.orientation commitment) ∧
    ¬ ((∀ L : LinearExtension,
      OrientedStop admissibleTarget (InFiniteNarrowedScope inScope)
        L.orientation commitment) <->
      ParetoGreatestIn value feasible true) := by
  constructor
  · exact
      ⟨by simp [feasible], rfl, rfl,
        fun action _ => ⟨Set.mem_univ action, True.intro⟩,
        true_pareto_maximal, true_pareto_greatest, ⟨linearExtension⟩⟩
  constructor
  · intro equivalence
    rcases equivalence.mp true_pareto_maximal with ⟨L, stop⟩
    exact no_linear_extension_stops_at_true L stop
  · intro equivalence
    have allStop := equivalence.mpr true_pareto_greatest
    exact no_linear_extension_stops_at_true linearExtension
      (allStop linearExtension)

/- The checked finite model witnesses both the theorem domain and every
top-level hypothesis in the refutation certificate. -/
noncomputable example : OP5Countermodel.LinearExtension :=
  OP5Countermodel.linearExtension

example :
    ParetoMaximalIn OP5Countermodel.value OP5Countermodel.feasible true ∧
      ParetoGreatestIn OP5Countermodel.value OP5Countermodel.feasible true :=
  ⟨OP5Countermodel.true_pareto_maximal,
    OP5Countermodel.true_pareto_greatest⟩

#print axioms op5_pareto_stop_linear_extension_equivalences_refuted

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
