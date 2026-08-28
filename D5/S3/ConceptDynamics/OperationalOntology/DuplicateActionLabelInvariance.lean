/- GID: D5/S3/ConceptDynamics/OperationalOntology/DuplicateActionLabelInvariance
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/OperationalOntology/DuplicateActionLabelInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Duplicate action behaviors preserve the effective quotient and finite capacity. -/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-26):
   * Repository name and body-shape searches found no existing declaration for
     duplicated action labels or the induced quotient map.
   * `ControlQuotientUniversalMinimality.controlProfile` is state-indexed and
     concerns a monoid action, while the source here quotients action labels by
     equality of their full continuation profiles.
   * Exact pinned-Mathlib hits `Quotient.map`, `Quotient.sound`,
     `Equiv.ofBijective`, and `Fintype.card_congr` provide the canonical quotient
     map, its inverse laws, and the finite-cardinality transport used below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.OperationalOntology.DuplicateActionLabelInvariance

/-- The canonical map from the original action-profile quotient to the
extended quotient, induced by retaining every original label. -/
def actionLabelQuotientMap
    {Action ExtendedAction Continuation Outcome : Type*}
    (profile : Action -> Continuation -> Outcome)
    (extendedProfile : ExtendedAction -> Continuation -> Outcome)
    (retain : Action -> ExtendedAction)
    (representative : ExtendedAction -> Action)
    (retracts : Function.LeftInverse representative retain)
    (duplicates : forall action,
      extendedProfile action = profile (representative action)) :
    Quotient (Setoid.ker profile) ->
      Quotient (Setoid.ker extendedProfile) :=
  Quotient.map retain (by
    intro first second sameProfile
    change extendedProfile (retain first) = extendedProfile (retain second)
    rw [duplicates, duplicates, retracts first, retracts second]
    exact sameProfile)

/-- Adding finitely many labels whose complete continuation profiles duplicate
existing behaviors leaves the effective action quotient and its base-two
log-cardinality capacity unchanged. -/
theorem duplicate_action_labels_preserve_effective_space
    {Action ExtendedAction Continuation Outcome : Type*}
    [Finite Action] [Finite ExtendedAction]
    (profile : Action -> Continuation -> Outcome)
    (extendedProfile : ExtendedAction -> Continuation -> Outcome)
    (retain : Action -> ExtendedAction)
    (representative : ExtendedAction -> Action)
    (retracts : Function.LeftInverse representative retain)
    (duplicates : forall action,
      extendedProfile action = profile (representative action)) :
    Function.Bijective
        (actionLabelQuotientMap profile extendedProfile retain representative
          retracts duplicates) ∧
      Real.logb 2 (Nat.card (Quotient (Setoid.ker profile))) =
        Real.logb 2
          (Nat.card (Quotient (Setoid.ker extendedProfile))) := by
  let returnToOriginal :
      Quotient (Setoid.ker extendedProfile) -> Quotient (Setoid.ker profile) :=
    Quotient.map representative (by
      intro first second sameProfile
      change profile (representative first) = profile (representative second)
      rw [← duplicates first, ← duplicates second]
      exact sameProfile)
  have leftInverse : Function.LeftInverse returnToOriginal
      (actionLabelQuotientMap profile extendedProfile retain representative
        retracts duplicates) := by
    intro actionClass
    refine Quotient.inductionOn actionClass ?_
    intro action
    apply Quotient.sound
    change profile (representative (retain action)) = profile action
    rw [retracts action]
  have rightInverse : Function.RightInverse returnToOriginal
      (actionLabelQuotientMap profile extendedProfile retain representative
        retracts duplicates) := by
    intro actionClass
    refine Quotient.inductionOn actionClass ?_
    intro action
    apply Quotient.sound
    change extendedProfile (retain (representative action)) =
      extendedProfile action
    rw [duplicates, duplicates, retracts (representative action)]
  have quotientMapBijective : Function.Bijective
      (actionLabelQuotientMap profile extendedProfile retain representative
        retracts duplicates) :=
    ⟨leftInverse.injective, rightInverse.surjective⟩
  refine ⟨quotientMapBijective, ?_⟩
  rw [Nat.card_congr
    (Equiv.ofBijective
      (actionLabelQuotientMap profile extendedProfile retain representative
        retracts duplicates)
      quotientMapBijective)]

#print axioms actionLabelQuotientMap
#print axioms duplicate_action_labels_preserve_effective_space

end D5.S3.ConceptDynamics.OperationalOntology.DuplicateActionLabelInvariance
