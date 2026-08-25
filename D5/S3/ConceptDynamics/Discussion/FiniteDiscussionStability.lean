/- GID: D5/S3/ConceptDynamics/Discussion/FiniteDiscussionStability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Discussion/FiniteDiscussionStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite discussion has at most the initially unresolved number of strict refinements. -/

import D5.S3.ConceptDynamics.StrictRefinementCapability
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite

/- Library-search audit trail (2026-08-21):
   * Repository search found and reuses the exact family definitions
     `ConceptJoinUniversal.Refines` and `StrictRefinementCapability.StrictRefinement`.
   * Repository search found the adjacent specialized bound
     `finite_observation_refinement_and_stability_bound`, but its iterated-observation
     hypotheses do not cover an arbitrary discussion of concept readouts.
   * Pinned Mathlib search found `Nat.bijective_iff_surjective_and_card` for turning
     an equal-cardinality surjective factor into the forbidden reverse refinement.
   * No repository or pinned-Mathlib declaration directly packages the claimed discussion bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Discussion.FiniteDiscussionStability

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.StrictRefinementCapability

private theorem strict_refinement_card_lt
    {X C D : Type*} [Finite X]
    (q_C : Concept X C) (q_D : Concept X D)
    (effective_C : Function.Surjective q_C)
    (effective_D : Function.Surjective q_D)
    (strict : StrictRefinement q_C q_D) :
    Nat.card C < Nat.card D := by
  letI : Finite C := Finite.of_surjective q_C effective_C
  letI : Finite D := Finite.of_surjective q_D effective_D
  rcases strict with ⟨⟨factor, hfactor⟩, noReverse⟩
  have factorSurjective : Function.Surjective factor := by
    intro coordinate
    obtain ⟨state, hstate⟩ := effective_C coordinate
    refine ⟨q_D state, ?_⟩
    have hfactorAt : q_C state = factor (q_D state) := by
      change q_C state = factor (q_D state)
      exact congrFun hfactor state
    exact hfactorAt.symm.trans hstate
  have cardLe : Nat.card C <= Nat.card D :=
    Nat.card_le_card_of_surjective factor factorSurjective
  refine lt_of_le_of_ne cardLe ?_
  intro cardEq
  apply noReverse
  have factorBijective : Function.Bijective factor :=
    (Nat.bijective_iff_surjective_and_card factor).2
      ⟨factorSurjective, cardEq.symm⟩
  let reverse : C -> D := fun coordinate =>
    q_D (Classical.choose (effective_C coordinate))
  refine ⟨reverse, ?_⟩
  funext state
  apply factorBijective.1
  change factor (q_D state) = factor (reverse (q_C state))
  calc
    factor (q_D state) = q_C state := by
      have hfactorAt := congrFun hfactor state
      change q_C state = factor (q_D state) at hfactorAt
      exact hfactorAt.symm
    _ = q_C (Classical.choose (effective_C (q_C state))) :=
      (Classical.choose_spec (effective_C (q_C state))).symm
    _ = factor (reverse (q_C state)) := by
      change q_C (Classical.choose (effective_C (q_C state))) =
        factor (q_D (Classical.choose (effective_C (q_C state))))
      have hfactorAt :=
        congrFun hfactor (Classical.choose (effective_C (q_C state)))
      change q_C (Classical.choose (effective_C (q_C state))) =
        factor (q_D (Classical.choose (effective_C (q_C state)))) at hfactorAt
      exact hfactorAt

private theorem strict_fin_sequence_length_bound
    {n : Nat} (rank : Fin (n + 1) -> Nat)
    (step : forall i : Fin n, rank i.castSucc < rank i.succ) :
    n + rank 0 <= rank (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n inductionHypothesis =>
      let initialSegment : Fin (n + 1) -> Nat := fun i => rank i.castSucc
      have prefixStep : forall i : Fin n,
          initialSegment i.castSucc < initialSegment i.succ := by
        intro i
        change rank i.castSucc.castSucc < rank i.succ.castSucc
        have indexEq : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
        rw [← indexEq]
        exact step i.castSucc
      have prefixBound := inductionHypothesis initialSegment prefixStep
      have lastStep := step (Fin.last n)
      have prefixBound' :
          n + rank 0 <= rank (Fin.castSucc (Fin.last n)) := by
        calc
          n + rank 0 = n + initialSegment 0 := by
            exact congrArg (fun value => n + value) (congrArg rank (Fin.ext rfl)).symm
          _ <= initialSegment (Fin.last n) := prefixBound
          _ = rank (Fin.castSucc (Fin.last n)) := rfl
      have lastStep' :
          rank (Fin.castSucc (Fin.last n)) < rank (Fin.last (n + 1)) := by
        have indexEq : (Fin.last n).succ = Fin.last (n + 1) := Fin.ext rfl
        rw [← indexEq]
        exact lastStep
      omega

/-- In a discussion on a finite state space, if every nonredundant message strictly
refines the current effective concept, then the number of strict information-growth
steps is at most the number of states not already distinguished by the initial concept. -/
theorem finite_discussion_stability
    {X : Type*} [Fintype X] {steps : Nat}
    (Coordinate : Fin (steps + 1) -> Type*)
    (concept : (i : Fin (steps + 1)) -> Concept X (Coordinate i))
    (effective : forall i, Function.Surjective (concept i))
    (strict : forall i : Fin steps,
      StrictRefinement (concept i.castSucc) (concept i.succ)) :
    steps <= Fintype.card X - Nat.card (Set.range (concept 0)) := by
  let rank : Fin (steps + 1) -> Nat := fun i => Nat.card (Coordinate i)
  have rankStep : forall i : Fin steps, rank i.castSucc < rank i.succ := by
    intro i
    exact strict_refinement_card_lt (concept i.castSucc) (concept i.succ)
      (effective i.castSucc) (effective i.succ) (strict i)
  have growthBound := strict_fin_sequence_length_bound rank rankStep
  have finalBound : Nat.card (Coordinate (Fin.last steps)) <= Fintype.card X := by
    simpa only [Nat.card_eq_fintype_card] using
      Nat.card_le_card_of_surjective (concept (Fin.last steps))
        (effective (Fin.last steps))
  have totalBound : steps + Nat.card (Coordinate 0) <= Fintype.card X := by
    have growthBound' :
        steps + Nat.card (Coordinate 0) <= Nat.card (Coordinate (Fin.last steps)) := by
      simpa only [rank] using growthBound
    exact growthBound'.trans finalBound
  let initialRangeEquiv : Set.range (concept 0) ≃ Coordinate 0 :=
    Equiv.ofBijective Subtype.val
      ⟨Subtype.val_injective, by
        intro coordinate
        obtain ⟨state, hstate⟩ := effective 0 coordinate
        exact ⟨⟨coordinate, state, hstate⟩, rfl⟩⟩
  have initialCard : Nat.card (Set.range (concept 0)) = Nat.card (Coordinate 0) :=
    Nat.card_congr initialRangeEquiv
  rw [initialCard]
  omega

private def oneStepCoordinate : Fin 2 -> Type :=
  Fin.cases Unit (fun _ => Bool)

private def oneStepConcept : (i : Fin 2) -> Concept Bool (oneStepCoordinate i) :=
  Fin.cases (fun _ => ()) (fun _ => id)

/-- A constant concept followed by the identity concept realizes one strict step
and attains the bound `1 = |Bool| - |Unit|`. -/
example :
    1 <= Fintype.card Bool - Nat.card (Set.range (oneStepConcept 0)) := by
  apply finite_discussion_stability oneStepCoordinate oneStepConcept
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Function.Surjective (fun _ : Bool => ())
      intro coordinate
      exact ⟨false, Subsingleton.elim _ coordinate⟩
    · change Function.Surjective (id : Bool -> Bool)
      exact Function.surjective_id
  · intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change StrictRefinement (fun _ : Bool => ()) (id : Concept Bool Bool)
    constructor
    · exact ⟨fun _ => (), rfl⟩
    · rintro ⟨factor, hfactor⟩
      apply Bool.false_ne_true
      calc
        false = factor () := by
          simpa only [oneStepConcept, oneStepCoordinate, Function.comp_apply, id_eq] using
            congrFun hfactor false
        _ = true := by
          simpa only [oneStepConcept, oneStepCoordinate, Function.comp_apply, id_eq] using
            (congrFun hfactor true).symm

#print axioms finite_discussion_stability

end D5.S3.ConceptDynamics.Discussion.FiniteDiscussionStability
