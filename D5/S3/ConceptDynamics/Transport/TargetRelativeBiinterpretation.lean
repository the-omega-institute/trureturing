/- GID: D5/S3/ConceptDynamics/Transport/TargetRelativeBiinterpretation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transport/TargetRelativeBiinterpretation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Mutual target recovery transports answers without requiring state isomorphism. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-23):
   * The canonical concept carrier and factorization relation are `Concept` and
     `Refines` from `ConceptJoinUniversal`; they are imported rather than
     redeclared.
   * `AnswerabilityCriterion.answerability_criterion` characterizes the same
     factorization by fiber constancy, while
     `ConservativeExtensionAnswerability.answerability_transports_along_surjection`
     handles a one-way surjective pullback. Neither states mutual target-relative
     recovery or the non-isomorphic countermodel below.
   * Pinned Mathlib's `Function.Bijective.injective` is applied directly to
     refute bijectivity of each concrete translation. No exact combined theorem
     was found in the repository or pinned Mathlib. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Transport.TargetRelativeBiinterpretation

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- A concrete translation that erases the second internal coordinate. -/
def eraseSecondCoordinate : Bool × Bool → Bool × Bool :=
  fun state => (state.1, false)

/-- The reverse concrete translation restores a different fixed hidden coordinate. -/
def setSecondTrueCoordinate : Bool × Bool → Bool × Bool :=
  fun state => (state.1, true)

/-- Both models expose only the first coordinate to the target family. -/
def firstCoordinateTarget : Concept (Bool × Bool) Bool :=
  Prod.fst

/-- Mutual recovery of every member of two target families makes each source
target factor through the forward translation and each target-model target
factor through the reverse translation. A concrete two-coordinate model shows
that this problem-relative equivalence can hold even when neither translation
is bijective and neither composite is the identity on internal states. -/
theorem target_relative_biinterpretation_transports_answerability :
    (∀ {X Y SourceIndex TargetIndex SourceValue TargetValue : Type*}
        (h : X → Y) (k : Y → X)
        (sourceTargets : SourceIndex → Concept X SourceValue)
        (targetTargets : TargetIndex → Concept Y TargetValue),
      ((∀ i, (sourceTargets i ∘ k) ∘ h = sourceTargets i) →
        ∀ i, Refines (sourceTargets i) h) ∧
      ((∀ j, (targetTargets j ∘ h) ∘ k = targetTargets j) →
        ∀ j, Refines (targetTargets j) k)) ∧
      ((firstCoordinateTarget ∘ setSecondTrueCoordinate) ∘
          eraseSecondCoordinate = firstCoordinateTarget) ∧
      ((firstCoordinateTarget ∘ eraseSecondCoordinate) ∘
          setSecondTrueCoordinate = firstCoordinateTarget) ∧
      ¬Function.Bijective eraseSecondCoordinate ∧
      ¬Function.Bijective setSecondTrueCoordinate ∧
      setSecondTrueCoordinate ∘ eraseSecondCoordinate ≠ id ∧
      eraseSecondCoordinate ∘ setSecondTrueCoordinate ≠ id := by
  constructor
  · intro X Y SourceIndex TargetIndex SourceValue TargetValue
      h k sourceTargets targetTargets
    constructor
    · intro sourceRecovery i
      exact ⟨sourceTargets i ∘ k, (sourceRecovery i).symm⟩
    · intro targetRecovery j
      exact ⟨targetTargets j ∘ h, (targetRecovery j).symm⟩
  constructor
  · funext state
    rfl
  constructor
  · funext state
    rfl
  constructor
  · intro hbijective
    have himages :
        eraseSecondCoordinate (false, false) =
          eraseSecondCoordinate (false, true) := rfl
    have hequal := hbijective.injective himages
    exact Bool.false_ne_true (congrArg Prod.snd hequal)
  constructor
  · intro hbijective
    have himages :
        setSecondTrueCoordinate (false, false) =
          setSecondTrueCoordinate (false, true) := rfl
    have hequal := hbijective.injective himages
    exact Bool.false_ne_true (congrArg Prod.snd hequal)
  constructor
  · intro hidentity
    have hequal := congrFun hidentity (false, false)
    exact Bool.false_ne_true (congrArg Prod.snd hequal).symm
  · intro hidentity
    have hequal := congrFun hidentity (false, true)
    exact Bool.false_ne_true (congrArg Prod.snd hequal)

/-- The concrete internal state carrier is inhabited. -/
example : Bool × Bool := (false, false)

/-- Identity translations witness satisfiability of both recovery premises for
arbitrary target families. -/
example {Index Value : Type*} (targets : Index → Concept Bool Value) :
    (∀ i, (targets i ∘ id) ∘ id = targets i) := by
  intro i
  rfl

#print axioms target_relative_biinterpretation_transports_answerability

end D5.S3.ConceptDynamics.Transport.TargetRelativeBiinterpretation
