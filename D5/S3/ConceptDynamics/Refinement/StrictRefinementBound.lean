/- GID: D5/S3/ConceptDynamics/Refinement/StrictRefinementBound
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Refinement/StrictRefinementBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite states permit at most their cardinal deficit many strict refinements. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard

/- Library-search audit trail (2026-08-21):
   * `rg -n "strict refinement|finite termination|image.*card|card.*image" D5 -g '*.lean'`
     found adjacent `finite_monotone_iteration_reaches_fixed_point`, but no theorem carrying the
     sharp `|X| - |range C₀|` bound.
   * The corresponding pinned-Mathlib search found `Nat.card_le_card_of_surjective`,
     `Finite.card_range_le`, and `Fin.strictMono_iff_lt_succ`; all three are applied below.
   * The repository's established `Concept` readout definition is imported and reused directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Refinement.StrictRefinementBound

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- A readout strictly refines another when it preserves all distinctions and
splits at least one old equivalence class. -/
def StrictlyRefines {X B : Type*} (coarse fine : Concept X B) : Prop :=
  (∀ ⦃x y : X⦄, fine x = fine y → coarse x = coarse y) ∧
    ∃ x y : X, coarse x = coarse y ∧ fine x ≠ fine y

/-- Every strict refinement of a finite readout strictly increases the number
of represented equivalence classes. -/
lemma range_card_strictly_increases
    {X B : Type*} [Finite X] (coarse fine : Concept X B)
    (strict : StrictlyRefines coarse fine) :
    Nat.card (Set.range coarse) < Nat.card (Set.range fine) := by
  classical
  letI : Finite (Set.range coarse) := Finite.Set.finite_range coarse
  letI : Finite (Set.range fine) := Finite.Set.finite_range fine
  let descend : Set.range fine → Set.range coarse := fun coordinate =>
    ⟨coarse (Classical.choose coordinate.property),
      ⟨Classical.choose coordinate.property, rfl⟩⟩
  have descend_surjective : Function.Surjective descend := by
    rintro ⟨_, x, rfl⟩
    let coordinate : Set.range fine := ⟨fine x, ⟨x, rfl⟩⟩
    refine ⟨coordinate, Subtype.ext ?_⟩
    exact strict.1 (Classical.choose_spec coordinate.property)
  have descend_not_injective : ¬Function.Injective descend := by
    obtain ⟨x, y, hcoarse, hfine⟩ := strict.2
    let xCoordinate : Set.range fine := ⟨fine x, ⟨x, rfl⟩⟩
    let yCoordinate : Set.range fine := ⟨fine y, ⟨y, rfl⟩⟩
    intro hinjective
    apply hfine
    have sameDescended : descend xCoordinate = descend yCoordinate := by
      apply Subtype.ext
      calc
        coarse (Classical.choose xCoordinate.property) = coarse x :=
          strict.1 (Classical.choose_spec xCoordinate.property)
        _ = coarse y := hcoarse
        _ = coarse (Classical.choose yCoordinate.property) :=
          (strict.1 (Classical.choose_spec yCoordinate.property)).symm
    exact congrArg Subtype.val (hinjective sameDescended)
  have card_le : Nat.card (Set.range coarse) ≤ Nat.card (Set.range fine) :=
    Nat.card_le_card_of_surjective descend descend_surjective
  exact card_le.lt_of_ne fun card_eq =>
    descend_not_injective
      (descend_surjective.bijective_of_nat_card_le card_eq.ge).1

private lemma strictMono_fin_add_le_last {n : Nat}
    (f : Fin (n + 1) → Nat) (strict : StrictMono f) :
    n + f 0 ≤ f (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n inductionHypothesis =>
      let initialSegment : Fin (n + 1) → Nat := fun i => f i.castSucc
      have initialSegmentStrict : StrictMono initialSegment :=
        strict.comp Fin.strictMono_castSucc
      have initialSegmentBound :=
        inductionHypothesis initialSegment initialSegmentStrict
      have finalStep :
          f (Fin.castSucc (Fin.last n)) < f (Fin.last (n + 1)) := by
        apply strict
        exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self n)
      change n + 1 + f 0 ≤ f (Fin.last (n + 1))
      change n + initialSegment 0 ≤ initialSegment (Fin.last n) at initialSegmentBound
      change initialSegment (Fin.last n) < f (Fin.last (n + 1)) at finalStep
      have initialZero : initialSegment 0 = f 0 := rfl
      omega

/-- The number of strict refinement steps is at most the number of states
minus the number of equivalence classes represented by the initial readout. -/
theorem strict_refinement_steps_le_card_sub_initial_image
    {X B : Type*} [Finite X] (steps : Nat)
    (readout : Fin (steps + 1) → Concept X B)
    (strict : ∀ i : Fin steps,
      StrictlyRefines (readout i.castSucc) (readout i.succ)) :
    steps ≤ Nat.card X - Nat.card (Set.range (readout 0)) := by
  let classCount : Fin (steps + 1) → Nat := fun i =>
    Nat.card (Set.range (readout i))
  have classCountStrict : StrictMono classCount :=
    Fin.strictMono_iff_lt_succ.mpr fun i =>
      range_card_strictly_increases (readout i.castSucc) (readout i.succ) (strict i)
  have growthBound :
      steps + Nat.card (Set.range (readout 0)) ≤
        Nat.card (Set.range (readout (Fin.last steps))) := by
    simpa only [classCount] using
      strictMono_fin_add_le_last classCount classCountStrict
  have finalBound :
      Nat.card (Set.range (readout (Fin.last steps))) ≤ Nat.card X :=
    Finite.card_range_le (readout (Fin.last steps))
  exact Nat.le_sub_of_add_le (growthBound.trans finalBound)

/-- A constant Boolean readout followed by the identity realizes one strict
refinement, so the hypotheses are jointly satisfiable. -/
example :
    let readout : Fin 2 → Concept Bool Bool := fun i =>
      if i = 0 then fun _ => false else id
    1 ≤ Nat.card Bool - Nat.card (Set.range (readout 0)) := by
  let readout : Fin 2 → Concept Bool Bool := fun i =>
    if i = 0 then fun _ => false else id
  apply strict_refinement_steps_le_card_sub_initial_image 1 readout
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  constructor
  · intro x y _
    simp [readout]
  · exact ⟨false, true, by simp [readout], by simp [readout]⟩

#print axioms strict_refinement_steps_le_card_sub_initial_image

end D5.S3.ConceptDynamics.Refinement.StrictRefinementBound
