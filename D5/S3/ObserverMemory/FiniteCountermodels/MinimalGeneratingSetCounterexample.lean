/- GID: D5/S3/ObserverMemory/FiniteCountermodels/MinimalGeneratingSetCounterexample
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/FiniteCountermodels/MinimalGeneratingSetCounterexample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Boolean-square concepts have deletion-minimal generators of sizes one and two. -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/- Library-search audit trail (2026-08-21):
   * The exact source-shaped query `minimal_generating_set` has no hit in D5
     or the active frozen ledger.
   * Searches for finite closure, top_X, and coordinate-generator statements
     found no matching declaration; the nearby observer-memory results use
     different quotient or factorization predicates.
   * The local closure predicate below is the finite source closure: a family
     generates top_X when its joint observations separate every pair of states.
     Finset.erase supplies the finite proper-subgenerator test.
 -/

namespace D5.S3.ObserverMemory.FiniteCountermodels.MinimalGeneratingSetCounterexample

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev State := Bool × Bool

instance : Fintype State := inferInstance

instance : DecidableEq State := inferInstance

abbrev ConceptValue := State ⊕ Bool

instance : Fintype ConceptValue := inferInstance

instance : DecidableEq ConceptValue := inferInstance

abbrev Concept := State → ConceptValue

instance : Fintype Concept := Pi.instFintype

instance : DecidableEq Concept := Fintype.decidablePiFintype

/-- The identity concept retains the whole Boolean-square state. -/
def identityConcept (x : State) : ConceptValue := .inl x

/-- The first coordinate concept retains only the first bit. -/
def firstCoordinateConcept (x : State) : ConceptValue := .inr x.1

/-- The second coordinate concept retains only the second bit. -/
def secondCoordinateConcept (x : State) : ConceptValue := .inr x.2

/-- A finite family generates top_X when its joint readout separates states. -/
def generatedTop (S : Finset Concept) : Prop :=
  ∀ x y : State, (∀ c ∈ S, c x = c y) → x = y

/-- Finite minimality: deleting any one member destroys generation of top_X. -/
def minimalGeneratingSet (S : Finset Concept) : Prop :=
  generatedTop S ∧ ∀ c ∈ S, ¬ generatedTop (S.erase c)

/-- The identity alone and the two coordinates jointly generate top_X, and both
families are deletion-minimal with different cardinalities. -/
theorem boolean_square_has_minimal_generators_of_sizes_one_and_two :
    generatedTop
        ({identityConcept, firstCoordinateConcept, secondCoordinateConcept} : Finset Concept) ∧
      minimalGeneratingSet ({identityConcept} : Finset Concept) ∧
      minimalGeneratingSet
        ({firstCoordinateConcept, secondCoordinateConcept} : Finset Concept) ∧
      ({identityConcept} : Finset Concept).card = 1 ∧
      ({firstCoordinateConcept, secondCoordinateConcept} : Finset Concept).card = 2 ∧
      (1 : Nat) ≠ 2 := by
  have hIdentity : generatedTop ({identityConcept} : Finset Concept) := by
    intro x y h
    have hxy := h identityConcept (by simp)
    simpa [identityConcept] using hxy
  have hCoordinates :
      generatedTop ({firstCoordinateConcept, secondCoordinateConcept} : Finset Concept) := by
    intro x y h
    have hFirst := h firstCoordinateConcept (by simp)
    have hSecond := h secondCoordinateConcept (by simp)
    have hFirstCoord : x.1 = y.1 := by
      simpa [firstCoordinateConcept] using hFirst
    have hSecondCoord : x.2 = y.2 := by
      simpa [secondCoordinateConcept] using hSecond
    exact Prod.ext hFirstCoord hSecondCoord
  have hEmpty : ¬ generatedTop (∅ : Finset Concept) := by
    intro h
    have hxy := h (false, false) (false, true) (by simp)
    exact Bool.noConfusion (congrArg Prod.snd hxy)
  have hDropFirst :
      ¬ generatedTop ({secondCoordinateConcept} : Finset Concept) := by
    intro h
    have hxy := h (false, false) (true, false) (by
      intro c hc
      have hc' : c = secondCoordinateConcept := by simpa using hc
      subst c
      simp [secondCoordinateConcept])
    exact Bool.noConfusion (congrArg Prod.fst hxy)
  have hDropSecond :
      ¬ generatedTop ({firstCoordinateConcept} : Finset Concept) := by
    intro h
    have hxy := h (false, false) (false, true) (by
      intro c hc
      have hc' : c = firstCoordinateConcept := by simpa using hc
      subst c
      simp [firstCoordinateConcept])
    exact Bool.noConfusion (congrArg Prod.snd hxy)
  have hAll : generatedTop
      ({identityConcept, firstCoordinateConcept, secondCoordinateConcept} : Finset Concept) := by
    intro x y h
    apply hIdentity x y
    intro c hc
    have hc' : c = identityConcept := by simpa using hc
    subst c
    exact h identityConcept (by simp)
  have hIdentityMinimal : minimalGeneratingSet ({identityConcept} : Finset Concept) := by
    refine ⟨hIdentity, ?_⟩
    intro c hc
    have hc' : c = identityConcept := by simpa using hc
    subst c
    simpa using hEmpty
  have hDistinct : firstCoordinateConcept ≠ secondCoordinateConcept := by
    intro h
    have hxy := congrFun h (true, false)
    have hfalse : (true : Bool) = false := by
      simpa [firstCoordinateConcept, secondCoordinateConcept] using hxy
    cases hfalse
  have hCoordinatesMinimal :
      minimalGeneratingSet ({firstCoordinateConcept, secondCoordinateConcept} : Finset Concept) := by
    have hEraseFirst :
      ({firstCoordinateConcept, secondCoordinateConcept} : Finset Concept).erase
            firstCoordinateConcept = {secondCoordinateConcept} := by
      ext c
      simp [hDistinct, Ne.symm hDistinct]
    have hEraseSecond :
        ({firstCoordinateConcept, secondCoordinateConcept} : Finset Concept).erase
            secondCoordinateConcept = {firstCoordinateConcept} := by
      rw [Finset.erase_insert_of_ne hDistinct]
      simp [hDistinct]
    refine ⟨hCoordinates, ?_⟩
    intro c hc
    rcases (by simpa [hDistinct, Ne.symm hDistinct] using hc :
      c = firstCoordinateConcept ∨ c = secondCoordinateConcept) with
      rfl | rfl
    · rw [hEraseFirst]
      exact hDropFirst
    · rw [hEraseSecond]
      exact hDropSecond
  exact ⟨hAll, hIdentityMinimal, hCoordinatesMinimal, by simp,
    by simp [hDistinct], by decide⟩

/-- A concrete state witnesses the finite source domain. -/
example : State := (false, false)

#print axioms boolean_square_has_minimal_generators_of_sizes_one_and_two

end D5.S3.ObserverMemory.FiniteCountermodels.MinimalGeneratingSetCounterexample
