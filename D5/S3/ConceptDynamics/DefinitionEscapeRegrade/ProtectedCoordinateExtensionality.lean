/- GID: D5/S3/ConceptDynamics/DefinitionEscapeRegrade/ProtectedCoordinateExtensionality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeRegrade/ProtectedCoordinateExtensionality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Seven dependent protected-coordinate projections characterize record equality. -/

import D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/- Library-search audit trail (2026-08-28):
   * Exact search for `ProtectedCoordinateTag`, `ProtectedCoordinateValue`,
     `protectedCoordinateAt`, `protected_coordinate_dependent_extensionality`,
     and `57.2-A` in `D5` found no existing Lean declaration.
   * Shape search for protected-coordinate extensionality found only the frozen
     `ProtectedCoordinates` carrier and its `protectedCoordinates` projection in
     TargetLaunderingCriterion. This module imports that carrier rather than
     declaring a second seven-field record.
   * The frozen target-laundering criteria concern temporal change, evaluation,
     and attribution. None states equality of the carrier from all seven
     dependent projections, so they are not duplicate proofs of this atom. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

open D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion

/-- The exhaustive finite labels for the seven protected coordinates. -/
inductive ProtectedCoordinateTag
  | targetChain
  | domain
  | epsilon
  | conditions
  | comparator
  | baseline
  | weightSpec
  deriving DecidableEq, Fintype

/-- The field type selected by each protected-coordinate label. -/
def ProtectedCoordinateValue
    (TargetChain Domain Epsilon Condition Comparator Baseline WeightSpec :
      Type u) :
    ProtectedCoordinateTag -> Type u
  | .targetChain => TargetChain
  | .domain => Domain
  | .epsilon => Epsilon
  | .conditions => Condition
  | .comparator => Comparator
  | .baseline => Baseline
  | .weightSpec => WeightSpec

/-- The dependent projection from the frozen protected-coordinate carrier. -/
def protectedCoordinateAt
    {TargetChain Domain Epsilon Condition Comparator Baseline WeightSpec :
      Type u}
    (coordinates :
      ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
        Baseline WeightSpec)
    (tag : ProtectedCoordinateTag) :
    ProtectedCoordinateValue TargetChain Domain Epsilon Condition Comparator
      Baseline WeightSpec tag :=
  match tag with
  | .targetChain => coordinates.targetChain
  | .domain => coordinates.domain
  | .epsilon => coordinates.epsilon
  | .conditions => coordinates.conditions
  | .comparator => coordinates.comparator
  | .baseline => coordinates.baseline
  | .weightSpec => coordinates.weightSpec

/-- Two protected-coordinate records are equal exactly when all seven dependent
projections agree. No field type needs decidable equality. -/
theorem protected_coordinate_dependent_extensionality
    {TargetChain Domain Epsilon Condition Comparator Baseline WeightSpec :
      Type u}
    (oldCoordinates newCoordinates :
      ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
        Baseline WeightSpec) :
    oldCoordinates = newCoordinates <->
      forall tag,
        protectedCoordinateAt oldCoordinates tag =
          protectedCoordinateAt newCoordinates tag := by
  constructor
  · rintro rfl tag
    rfl
  · intro equalAt
    cases oldCoordinates with
    | mk oldTargetChain oldDomain oldEpsilon oldConditions oldComparator
        oldBaseline oldWeightSpec =>
      cases newCoordinates with
      | mk newTargetChain newDomain newEpsilon newConditions newComparator
          newBaseline newWeightSpec =>
        have targetChainEq : oldTargetChain = newTargetChain := by
          simpa only [protectedCoordinateAt, ProtectedCoordinateValue] using
            equalAt ProtectedCoordinateTag.targetChain
        have domainEq : oldDomain = newDomain := by
          simpa only [protectedCoordinateAt, ProtectedCoordinateValue] using
            equalAt ProtectedCoordinateTag.domain
        have epsilonEq : oldEpsilon = newEpsilon := by
          simpa only [protectedCoordinateAt, ProtectedCoordinateValue] using
            equalAt ProtectedCoordinateTag.epsilon
        have conditionsEq : oldConditions = newConditions := by
          simpa only [protectedCoordinateAt, ProtectedCoordinateValue] using
            equalAt ProtectedCoordinateTag.conditions
        have comparatorEq : oldComparator = newComparator := by
          simpa only [protectedCoordinateAt, ProtectedCoordinateValue] using
            equalAt ProtectedCoordinateTag.comparator
        have baselineEq : oldBaseline = newBaseline := by
          simpa only [protectedCoordinateAt, ProtectedCoordinateValue] using
            equalAt ProtectedCoordinateTag.baseline
        have weightSpecEq : oldWeightSpec = newWeightSpec := by
          simpa only [protectedCoordinateAt, ProtectedCoordinateValue] using
            equalAt ProtectedCoordinateTag.weightSpec
        cases targetChainEq
        cases domainEq
        cases epsilonEq
        cases conditionsEq
        cases comparatorEq
        cases baselineEq
        cases weightSpecEq
        rfl

namespace FiniteWitness

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

example :
    protectedCoordinateAt allFalse .domain ≠
      protectedCoordinateAt changedDomain .domain := by
  change false ≠ true
  decide

example : allFalse ≠ changedDomain := by
  intro equalCoordinates
  have domainEq :=
    (protected_coordinate_dependent_extensionality allFalse changedDomain).mp
      equalCoordinates ProtectedCoordinateTag.domain
  exact Bool.false_ne_true domainEq

example :
    allFalse = allFalse <->
      forall tag,
        protectedCoordinateAt allFalse tag = protectedCoordinateAt allFalse tag :=
  protected_coordinate_dependent_extensionality allFalse allFalse

end FiniteWitness

#print axioms protected_coordinate_dependent_extensionality

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
