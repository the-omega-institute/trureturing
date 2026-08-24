/- GID: D5/S3/ConceptDynamics/Reporting/PublicCausalActivityCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Reporting/PublicCausalActivityCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One-step public dynamic equivalence is exactly public inertia; Boolean witnesses separate phenomenal difference from public causal activity in both directions, and an intervention-only action strictly refines the static public readout. -/

import D5.S3.ConceptDynamics.Reporting.PhenomenalSupervenience

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'public_causal_activity_criterion_and_separations' D5
     Golden/Frozen/accepted` returned no hit.
   * The public repository search found `supervenience_xor_zombie_witness`, whose
     constant-public Bool witness and `ZombieWitness` definition are reused below.
   * `ObservationInterventionSeparation` compares two causal models, while
     `DynamicClosureMinimality` proves a finite-word closure universal property;
     neither separates phenomenal difference, public causal activity, and inertia.
   * The targeted private-declaration search found no relevant private result.
   * Pinned Mathlib searches found Boolean evaluation lemmas but no declaration for
     public dynamic equivalence or these causal/phenomenal separation witnesses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Reporting.PublicCausalActivityCriterion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Reporting.PhenomenalSupervenience

/-- Two states are phenomenally different when their phenomenal readouts disagree. -/
def PhenomenallyDifferent {State Phenomenal : Type*}
    (phenomenal : Concept State Phenomenal) (x y : State) : Prop :=
  phenomenal x ≠ phenomenal y

/-- A pair is publicly causally active when an allowed action separates its public results. -/
def PubliclyCausallyActive {State Action Public : Type*}
    (intervene : Action -> State -> State) (publicReadout : Concept State Public)
    (x y : State) : Prop :=
  ∃ m, publicReadout (intervene m x) ≠ publicReadout (intervene m y)

/-- Public dynamic equivalence is equality of public results after every allowed action. -/
def PublicDynamicEquiv {State Action Public : Type*}
    (intervene : Action -> State -> State) (publicReadout : Concept State Public)
    (x y : State) : Prop :=
  ∀ m, publicReadout (intervene m x) = publicReadout (intervene m y)

/-- Public causal activity excludes membership in the same public dynamic class. -/
theorem public_causal_activity_excludes_dynamic_equivalence
    {State Action Public : Type*}
    (intervene : Action -> State -> State) (publicReadout : Concept State Public)
    (x y : State) :
    PubliclyCausallyActive intervene publicReadout x y ->
      ¬PublicDynamicEquiv intervene publicReadout x y := by
  rintro ⟨m, differentPublic⟩ sameDynamic
  exact differentPublic (sameDynamic m)

/-- Public dynamic equivalence is exactly public representational inertia. -/
theorem public_dynamic_equiv_iff_inert {State Action Public : Type*}
    (intervene : Action -> State -> State) (publicReadout : Concept State Public)
    (x y : State) :
    PublicDynamicEquiv intervene publicReadout x y ↔
      ∀ m, publicReadout (intervene m x) = publicReadout (intervene m y) := by
  rfl

/-- Public dynamic equivalence really is an equivalence relation on states. -/
theorem public_dynamic_equiv_is_equivalence {State Action Public : Type*}
    (intervene : Action -> State -> State) (publicReadout : Concept State Public) :
    Equivalence (PublicDynamicEquiv intervene publicReadout) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x m
    rfl
  · intro x y sameDynamic m
    exact (sameDynamic m).symm
  · intro x y z sameXY sameYZ m
    exact (sameXY m).trans (sameYZ m)

/-- The existing phenomenal zombie uses the identity action, so it remains publicly inert. -/
def zombieIntervention : Unit -> Bool -> Bool := fun _ state => state

/-- The inherited phenomenal readout distinguishes the two Boolean states. -/
def zombiePhenomenal : Concept Bool Bool := id

/-- The inherited joint public readout is constant on both Boolean states. -/
def zombiePublic : Concept Bool (Bool × Bool) :=
  conceptJoin (fun _ : Bool => false) (fun _ : Bool => false)

/-- The explicit zombie pair is phenomenally different but publicly inert and inactive. -/
theorem phenomenal_difference_with_public_inertia :
    ZombieWitness zombiePhenomenal zombiePublic ∧
      PhenomenallyDifferent zombiePhenomenal false true ∧
      PublicDynamicEquiv zombieIntervention zombiePublic false true ∧
      ¬PubliclyCausallyActive zombieIntervention zombiePublic false true := by
  refine ⟨?_, Bool.false_ne_true, ?_, ?_⟩
  · simpa [zombiePhenomenal, zombiePublic] using
      supervenience_xor_zombie_witness.{0, 0, 0, 0}.2.1
  · intro m
    cases m
    rfl
  · rintro ⟨m, differentPublic⟩
    exact differentPublic (by cases m; rfl)

/-- A constant phenomenal readout makes the active Boolean pair phenomenally equal. -/
def constantPhenomenal : Concept Bool Bool := fun _ => false

/-- The identity public readout exposes the Boolean state. -/
def identityPublic : Concept Bool Bool := id

/-- An active public pair can nevertheless have identical phenomenal readouts. -/
theorem public_activity_with_phenomenal_agreement :
    PubliclyCausallyActive zombieIntervention identityPublic false true ∧
      constantPhenomenal false = constantPhenomenal true ∧
      ¬PhenomenallyDifferent constantPhenomenal false true := by
  refine ⟨⟨(), Bool.false_ne_true⟩, rfl, ?_⟩
  intro differentPhenomenal
  exact differentPhenomenal rfl

/-- The static public readout sees only the first bit of a two-bit private state. -/
def hiddenBitPublic : Concept (Bool × Bool) Bool := Prod.fst

/-- This intervention copies the private second bit into the publicly visible first bit. -/
def revealHiddenBit : Unit -> Bool × Bool -> Bool × Bool :=
  fun _ state => (state.2, state.2)

/-- Static public equality is strictly coarser than the intervention-only dynamic class. -/
theorem static_public_equality_with_dynamic_separation :
    hiddenBitPublic (false, false) = hiddenBitPublic (false, true) ∧
      PubliclyCausallyActive revealHiddenBit hiddenBitPublic
        (false, false) (false, true) ∧
      ¬PublicDynamicEquiv revealHiddenBit hiddenBitPublic
        (false, false) (false, true) := by
  refine ⟨rfl, ⟨(), Bool.false_ne_true⟩, ?_⟩
  intro sameDynamic
  exact Bool.false_ne_true (sameDynamic ())

/-- The activity criterion, its inert characterization, and all three concrete separations. -/
theorem public_causal_activity_criterion_and_separations :
    (∀ {State Action Public : Type*}
      (intervene : Action -> State -> State) (publicReadout : Concept State Public)
      (x y : State), PubliclyCausallyActive intervene publicReadout x y ->
        ¬PublicDynamicEquiv intervene publicReadout x y) ∧
    (∀ {State Action Public : Type*}
      (intervene : Action -> State -> State) (publicReadout : Concept State Public)
      (x y : State), PublicDynamicEquiv intervene publicReadout x y ↔
        ∀ m, publicReadout (intervene m x) = publicReadout (intervene m y)) ∧
    Equivalence (PublicDynamicEquiv zombieIntervention zombiePublic) ∧
    (ZombieWitness zombiePhenomenal zombiePublic ∧
      PhenomenallyDifferent zombiePhenomenal false true ∧
      PublicDynamicEquiv zombieIntervention zombiePublic false true ∧
      ¬PubliclyCausallyActive zombieIntervention zombiePublic false true) ∧
    (PubliclyCausallyActive zombieIntervention identityPublic false true ∧
      constantPhenomenal false = constantPhenomenal true ∧
      ¬PhenomenallyDifferent constantPhenomenal false true) ∧
    (hiddenBitPublic (false, false) = hiddenBitPublic (false, true) ∧
      PubliclyCausallyActive revealHiddenBit hiddenBitPublic
        (false, false) (false, true) ∧
      ¬PublicDynamicEquiv revealHiddenBit hiddenBitPublic
        (false, false) (false, true)) := by
  refine
    ⟨?_, ?_, ?_, phenomenal_difference_with_public_inertia,
      public_activity_with_phenomenal_agreement,
      static_public_equality_with_dynamic_separation⟩
  · intro State Action Public intervene publicReadout x y
    exact
      public_causal_activity_excludes_dynamic_equivalence
        intervene publicReadout x y
  · intro State Action Public intervene publicReadout x y
    exact public_dynamic_equiv_iff_inert intervene publicReadout x y
  · exact public_dynamic_equiv_is_equivalence zombieIntervention zombiePublic

example :
    PubliclyCausallyActive revealHiddenBit hiddenBitPublic
      (false, false) (false, true) := by
  exact static_public_equality_with_dynamic_separation.2.1

#print axioms public_causal_activity_criterion_and_separations

end D5.S3.ConceptDynamics.Reporting.PublicCausalActivityCriterion
