/- GID: D5/S3/ConceptDynamics/DefinitionEscapeRegrade/CoordinateWitnessBundle
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeRegrade/CoordinateWitnessBundle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Closed nonempty coordinate witnesses exactly record changed protected coordinates. -/

import D5.S3.ConceptDynamics.DefinitionEscapeRegrade.ProtectedCoordinateExtensionality

/- Library-search audit trail (2026-08-29):
   * Exact and shape searches in `D5` found no existing declaration of
     `CoordinateWitnessBundle`, `HasClosedCoordinateWitnessBundle`, or the
     target equivalence.
   * The pinned mathlib supplies `Finset.filter_nonempty_iff`,
     `Finset.mem_filter`, and `Finset.mem_univ`, but no theorem specialized to
     this dependent seven-coordinate carrier.
   * This proof imports the frozen 57.2-A dependent extensionality theorem and
     uses the seven requested `DecidableEq` instances for the finite scan. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

open D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion

/-- A finite register of protected-coordinate labels that actually changed. -/
structure CoordinateWitnessBundle
    {TargetChain Domain Epsilon Condition Comparator Baseline WeightSpec :
      Type u}
    (oldCoordinates newCoordinates :
      ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
        Baseline WeightSpec) where
  changed : Finset ProtectedCoordinateTag
  sound :
    forall tag, tag ∈ changed ->
      protectedCoordinateAt oldCoordinates tag ≠
        protectedCoordinateAt newCoordinates tag

namespace CoordinateWitnessBundle

/-- Every genuinely changed protected coordinate is registered in the bundle. -/
def Closed
    {TargetChain Domain Epsilon Condition Comparator Baseline WeightSpec :
      Type u}
    {oldCoordinates newCoordinates :
      ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
        Baseline WeightSpec}
    (bundle : CoordinateWitnessBundle oldCoordinates newCoordinates) : Prop :=
  forall tag,
    protectedCoordinateAt oldCoordinates tag ≠
      protectedCoordinateAt newCoordinates tag ->
    tag ∈ bundle.changed

end CoordinateWitnessBundle

/-- A sound, complete, and nonempty register of changed protected coordinates. -/
def HasClosedCoordinateWitnessBundle
    {TargetChain Domain Epsilon Condition Comparator Baseline WeightSpec :
      Type u}
    (oldCoordinates newCoordinates :
      ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
        Baseline WeightSpec) : Prop :=
  exists bundle : CoordinateWitnessBundle oldCoordinates newCoordinates,
    CoordinateWitnessBundle.Closed bundle ∧ bundle.changed.Nonempty

private def protectedCoordinateTags : Finset ProtectedCoordinateTag :=
  {.targetChain, .domain, .epsilon, .conditions, .comparator, .baseline,
    .weightSpec}

@[reducible] private def protectedCoordinateEqualityDecidable
    {TargetChain Domain Epsilon Condition Comparator Baseline WeightSpec :
      Type u}
    [DecidableEq TargetChain]
    [DecidableEq Domain]
    [DecidableEq Epsilon]
    [DecidableEq Condition]
    [DecidableEq Comparator]
    [DecidableEq Baseline]
    [DecidableEq WeightSpec]
    (oldCoordinates newCoordinates :
      ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
        Baseline WeightSpec) :
    DecidablePred fun tag =>
      protectedCoordinateAt oldCoordinates tag =
        protectedCoordinateAt newCoordinates tag := by
  intro tag
  cases tag <;> simp only [protectedCoordinateAt, ProtectedCoordinateValue] <;>
    infer_instance

set_option linter.unusedDecidableInType false in
/-- A closed nonempty coordinate witness bundle exists exactly when the two
protected-coordinate records differ. -/
theorem has_closed_coordinate_witness_bundle_iff_ne
    {TargetChain Domain Epsilon Condition Comparator Baseline WeightSpec :
      Type u}
    [DecidableEq TargetChain]
    [DecidableEq Domain]
    [DecidableEq Epsilon]
    [DecidableEq Condition]
    [DecidableEq Comparator]
    [DecidableEq Baseline]
    [DecidableEq WeightSpec]
    (oldCoordinates newCoordinates :
      ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
        Baseline WeightSpec) :
    HasClosedCoordinateWitnessBundle oldCoordinates newCoordinates <->
      oldCoordinates ≠ newCoordinates := by
  constructor
  · rintro ⟨bundle, _, changedNonempty⟩ equalCoordinates
    subst newCoordinates
    obtain ⟨tag, tagMem⟩ := changedNonempty
    exact bundle.sound tag tagMem rfl
  · intro coordinatesNe
    letI : DecidablePred fun tag =>
        protectedCoordinateAt oldCoordinates tag =
          protectedCoordinateAt newCoordinates tag :=
      protectedCoordinateEqualityDecidable oldCoordinates newCoordinates
    let changedCoordinates : Finset ProtectedCoordinateTag :=
      protectedCoordinateTags.filter fun tag =>
        protectedCoordinateAt oldCoordinates tag ≠
          protectedCoordinateAt newCoordinates tag
    have changedSound :
        forall tag, tag ∈ changedCoordinates ->
          protectedCoordinateAt oldCoordinates tag ≠
            protectedCoordinateAt newCoordinates tag := by
      intro tag tagMem
      exact (Finset.mem_filter.mp tagMem).2
    have changedClosed :
        forall tag,
          protectedCoordinateAt oldCoordinates tag ≠
            protectedCoordinateAt newCoordinates tag ->
          tag ∈ changedCoordinates := by
      intro tag differs
      apply Finset.mem_filter.mpr
      constructor
      · cases tag <;> simp [protectedCoordinateTags]
      · exact differs
    have changedNonempty : changedCoordinates.Nonempty := by
      let nonemptyDecision : Decidable changedCoordinates.Nonempty :=
        Finset.decidableNonempty
      cases nonemptyDecision with
      | isFalse empty =>
        have allEqual :
            forall tag,
              protectedCoordinateAt oldCoordinates tag =
                protectedCoordinateAt newCoordinates tag := by
          intro tag
          let differenceDecision : Decidable
              (protectedCoordinateAt oldCoordinates tag ≠
                protectedCoordinateAt newCoordinates tag) := inferInstance
          cases differenceDecision with
          | isTrue differs =>
            exact False.elim (empty ⟨tag, changedClosed tag differs⟩)
          | isFalse equalNotNot =>
            exact Decidable.of_not_not equalNotNot
        exact False.elim
          (coordinatesNe
            ((protected_coordinate_dependent_extensionality
              oldCoordinates newCoordinates).mpr allEqual))
      | isTrue nonempty =>
        exact nonempty
    exact
      ⟨{ changed := changedCoordinates, sound := changedSound },
        changedClosed, changedNonempty⟩

namespace CoordinateBundleFiniteWitness

abbrev BooleanCoordinates :=
  ProtectedCoordinates Bool Bool Bool Bool Bool Bool Bool

def allFalse : BooleanCoordinates where
  targetChain := false
  domain := false
  epsilon := false
  conditions := false
  comparator := false
  baseline := false
  weightSpec := false

def changedDomain : BooleanCoordinates where
  targetChain := false
  domain := true
  epsilon := false
  conditions := false
  comparator := false
  baseline := false
  weightSpec := false

def emptyBundle : CoordinateWitnessBundle allFalse allFalse where
  changed := ∅
  sound := by simp

example : emptyBundle.changed = ∅ := rfl

example : allFalse ≠ changedDomain := by
  intro equalCoordinates
  have domainEq :=
    (protected_coordinate_dependent_extensionality allFalse changedDomain).mp
      equalCoordinates ProtectedCoordinateTag.domain
  exact Bool.false_ne_true domainEq

example : HasClosedCoordinateWitnessBundle allFalse changedDomain :=
  (has_closed_coordinate_witness_bundle_iff_ne allFalse changedDomain).mpr (by
    intro equalCoordinates
    have domainEq :=
      (protected_coordinate_dependent_extensionality allFalse changedDomain).mp
        equalCoordinates ProtectedCoordinateTag.domain
    exact Bool.false_ne_true domainEq)

example : ¬ HasClosedCoordinateWitnessBundle allFalse allFalse := by
  rw [has_closed_coordinate_witness_bundle_iff_ne]
  exact not_ne_iff.mpr rfl

end CoordinateBundleFiniteWitness

#print axioms has_closed_coordinate_witness_bundle_iff_ne

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
