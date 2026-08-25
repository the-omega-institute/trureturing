/- GID: D5/S3/ConceptDynamics/InvolutionLogic/AtomicNegationRigidity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InvolutionLogic/AtomicNegationRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite nonempty atomic-negation universe has exactly two elements. -/

import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/- Library-search audit trail (2026-08-25):
   * Pinned Mathlib supplies equivalences, finite-cardinality transport, and Bool.
   * Repository searches found no accepted structure characterizing when every
     singleton complement is represented by one point.
   * The theorem isolates the exceptional closure of point negation in a
     two-element universe. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InvolutionLogic.AtomicNegationRigidity

/-- An atomic negation assigns to every point the unique other point. -/
structure AtomicNegation (X : Type*) where
  neg : X → X
  other_iff : ∀ x y, y ≠ x ↔ y = neg x

namespace AtomicNegation

variable {X Y : Type*}

/-- Atomic negation has no fixed points. -/
theorem neg_ne (negation : AtomicNegation X) (x : X) :
    negation.neg x ≠ x :=
  (negation.other_iff x (negation.neg x)).2 rfl

/-- Atomic negation is automatically involutive. -/
theorem involutive (negation : AtomicNegation X) :
    Function.Involutive negation.neg := by
  intro x
  exact ((negation.other_iff (negation.neg x) x).1
    (negation.neg_ne x).symm).symm

/-- The complement of a singleton is the singleton containing its atomic negation. -/
theorem compl_singleton_eq_singleton
    (negation : AtomicNegation X) (x : X) :
    ({x} : Set X)ᶜ = {negation.neg x} := by
  ext y
  change y ≠ x ↔ y = negation.neg x
  exact negation.other_iff x y

/-- Transport atomic negation across an equivalence. -/
def transport (equiv : X ≃ Y) (negation : AtomicNegation Y) :
    AtomicNegation X where
  neg x := equiv.symm (negation.neg (equiv x))
  other_iff x y := by
    constructor
    · intro different
      have imageDifferent : equiv y ≠ equiv x := by
        intro imageEqual
        exact different (equiv.injective imageEqual)
      apply equiv.injective
      simpa using (negation.other_iff (equiv x) (equiv y)).1 imageDifferent
    · intro transportedEquality same
      have fixedImage : equiv x = negation.neg (equiv x) := by
        calc
          equiv x = equiv y := congrArg equiv same.symm
          _ = negation.neg (equiv x) := by
            simpa using congrArg equiv transportedEquality
      exact negation.neg_ne (equiv x) fixedImage.symm

/-- Boolean negation is the canonical atomic negation. -/
def bool : AtomicNegation Bool where
  neg value := !value
  other_iff x y := by
    cases x <;> cases y <;> decide

/-- Choosing one point identifies every atomic-negation universe with Bool. -/
noncomputable def equivBool (negation : AtomicNegation X) (anchor : X) :
    X ≃ Bool := by
  classical
  refine
    { toFun := fun x => if x = anchor then false else true
      invFun := fun value => match value with
        | false => anchor
        | true => negation.neg anchor
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    by_cases same : x = anchor
    · subst x
      simp
    · have other : x = negation.neg anchor :=
        (negation.other_iff anchor x).1 same
      simp [same, other, negation.neg_ne anchor]
  · intro value
    cases value <;> simp [negation.neg_ne anchor]

/-- On a nonempty type, atomic negation exists exactly when the type is equivalent to Bool. -/
theorem nonempty_iff_equiv_bool [Nonempty X] :
    Nonempty (AtomicNegation X) ↔ Nonempty (X ≃ Bool) := by
  constructor
  · rintro ⟨negation⟩
    exact ⟨negation.equivBool (Classical.choice (inferInstance : Nonempty X))⟩
  · rintro ⟨equiv⟩
    exact ⟨transport equiv bool⟩

/-- A finite nonempty atomic-negation universe has exactly two elements. -/
theorem card_eq_two [Fintype X] [Nonempty X]
    (negation : AtomicNegation X) : Fintype.card X = 2 := by
  classical
  let equiv := negation.equivBool (Classical.choice (inferInstance : Nonempty X))
  simpa using Fintype.card_congr equiv

#print axioms AtomicNegation.involutive
#print axioms AtomicNegation.nonempty_iff_equiv_bool
#print axioms AtomicNegation.card_eq_two

end AtomicNegation
end D5.S3.ConceptDynamics.InvolutionLogic.AtomicNegationRigidity
