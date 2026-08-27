/- GID: D5/S3/ConceptDynamics/TargetRisk/MaximumFactorCompatibleSubdomain
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/TargetRisk/MaximumFactorCompatibleSubdomain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Largest target-consistent fiber blocks give the sharp factor-compatible domain size. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold

/- Library-search audit trail (2026-08-27):
   * Repository searches for maximum factor-compatible subdomains, joint fiber
     blocks, and counterexample-free coverage found no exact whole theorem.
   * `DomainImmunizationAudit` constructs a singleton restricted domain but does
     not optimize its size. `fiberTargetValues` and `worstFiberDiversity` count
     distinct target values, rather than the states in a largest target block.
   * Exact pinned-Mathlib hits `Function.FactorsThrough`,
     `Finset.card_eq_sum_card_fiberwise`, `Finset.exists_mem_eq_sup`, and
     `Finset.le_sup` supply the canonical restriction test, fiber partition,
     attainable fiber maxima, and their upper bounds. No new definition or
     abbreviation is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.TargetRisk.MaximumFactorCompatibleSubdomain

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open scoped BigOperators

/-- For a finite state carrier, every subdomain on which the target factors
through the concept has size at most the sum of the largest target block in
each realized concept fiber, and selecting one largest block per fiber attains
that bound. The concept and target codomains need not be finite. -/
theorem maximum_factor_compatible_subdomain
    {X B Y : Type*} [Fintype X]
    (concept : Concept X B) (target : Concept X Y) :
    by
      classical
      exact
        (forall admitted : Finset X,
          Function.FactorsThrough
              (fun state : {x // x ∈ admitted} => target state.1)
              (fun state : {x // x ∈ admitted} => concept state.1) ->
            admitted.card <=
              ∑ b ∈ Finset.univ.image concept,
                (Finset.univ.filter fun x => concept x = b).sup
                  (fun representative =>
                    (Finset.univ.filter fun x =>
                      concept x = b ∧
                        target x = target representative).card)) ∧
        (exists admitted : Finset X,
          Function.FactorsThrough
              (fun state : {x // x ∈ admitted} => target state.1)
              (fun state : {x // x ∈ admitted} => concept state.1) ∧
            admitted.card =
              ∑ b ∈ Finset.univ.image concept,
                (Finset.univ.filter fun x => concept x = b).sup
                  (fun representative =>
                    (Finset.univ.filter fun x =>
                      concept x = b ∧
                        target x = target representative).card)) := by
  classical
  let conceptValues : Finset B := Finset.univ.image concept
  let blockSize : B -> X -> Nat := fun b representative =>
    (Finset.univ.filter fun x =>
      concept x = b ∧ target x = target representative).card
  let fiberMaximum : B -> Nat := fun b =>
    (Finset.univ.filter fun x => concept x = b).sup (blockSize b)
  change
    (forall admitted : Finset X,
      Function.FactorsThrough
          (fun state : {x // x ∈ admitted} => target state.1)
          (fun state : {x // x ∈ admitted} => concept state.1) ->
        admitted.card <= ∑ b ∈ conceptValues, fiberMaximum b) ∧
      (exists admitted : Finset X,
        Function.FactorsThrough
            (fun state : {x // x ∈ admitted} => target state.1)
            (fun state : {x // x ∈ admitted} => concept state.1) ∧
          admitted.card = ∑ b ∈ conceptValues, fiberMaximum b)
  have concept_mem_values (x : X) : concept x ∈ conceptValues := by
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  constructor
  · intro admitted factors
    have partition :
        admitted.card =
          ∑ b ∈ conceptValues,
            (admitted.filter fun x => concept x = b).card := by
      exact Finset.card_eq_sum_card_fiberwise fun x _ => concept_mem_values x
    rw [partition]
    apply Finset.sum_le_sum
    intro b inConceptValues
    by_cases fiberEmpty :
        (admitted.filter fun x => concept x = b) = ∅
    · simp [fiberEmpty]
    · have fiberNonempty :
          (admitted.filter fun x => concept x = b).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr fiberEmpty
      obtain ⟨representative, representativeInFiber⟩ := fiberNonempty
      have representativeInAdmitted : representative ∈ admitted :=
        (Finset.mem_filter.mp representativeInFiber).1
      have representativeConcept : concept representative = b :=
        (Finset.mem_filter.mp representativeInFiber).2
      have fiberSubsetBlock :
          admitted.filter (fun x => concept x = b) ⊆
            Finset.univ.filter (fun x =>
              concept x = b ∧ target x = target representative) := by
        intro x xInFiber
        have xInAdmitted : x ∈ admitted := (Finset.mem_filter.mp xInFiber).1
        have xConcept : concept x = b := (Finset.mem_filter.mp xInFiber).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ x, xConcept, ?_⟩
        exact factors
          (a := ⟨x, xInAdmitted⟩)
          (b := ⟨representative, representativeInAdmitted⟩)
          (xConcept.trans representativeConcept.symm)
      calc
        (admitted.filter fun x => concept x = b).card <=
            blockSize b representative := by
          exact Finset.card_le_card fiberSubsetBlock
        _ <= fiberMaximum b := by
          apply Finset.le_sup
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ representative, representativeConcept⟩
  · have realizedFiberNonempty (b : {b // b ∈ conceptValues}) :
        (Finset.univ.filter fun x => concept x = b.1).Nonempty := by
      rcases Finset.mem_image.mp b.2 with ⟨x, _xInUniverse, conceptX⟩
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, conceptX⟩⟩
    have winnerExists (b : {b // b ∈ conceptValues}) :
        exists winner : X,
          winner ∈ Finset.univ.filter (fun x => concept x = b.1) ∧
            fiberMaximum b.1 = blockSize b.1 winner := by
      exact Finset.exists_mem_eq_sup
        (Finset.univ.filter fun x => concept x = b.1)
        (realizedFiberNonempty b) (blockSize b.1)
    choose winner winnerInFiber winnerMaximum using winnerExists
    let admitted : Finset X := Finset.univ.filter fun x =>
      target x = target (winner ⟨concept x, concept_mem_values x⟩)
    refine ⟨admitted, ?_, ?_⟩
    · intro left right sameConcept
      have leftSelected :
          target left.1 =
            target (winner ⟨concept left.1, concept_mem_values left.1⟩) :=
        (Finset.mem_filter.mp left.2).2
      have rightSelected :
          target right.1 =
            target (winner ⟨concept right.1, concept_mem_values right.1⟩) :=
        (Finset.mem_filter.mp right.2).2
      have sameEffectiveConcept :
          (⟨concept left.1, concept_mem_values left.1⟩ :
              {b // b ∈ conceptValues}) =
            ⟨concept right.1, concept_mem_values right.1⟩ :=
        Subtype.ext sameConcept
      calc
        target left.1 =
            target (winner ⟨concept left.1, concept_mem_values left.1⟩) :=
          leftSelected
        _ = target (winner ⟨concept right.1, concept_mem_values right.1⟩) :=
          congrArg (fun b => target (winner b)) sameEffectiveConcept
        _ = target right.1 := rightSelected.symm
    · have partition :
          admitted.card =
            ∑ b ∈ conceptValues,
              (admitted.filter fun x => concept x = b).card := by
        exact Finset.card_eq_sum_card_fiberwise fun x _ => concept_mem_values x
      rw [partition]
      apply Finset.sum_congr rfl
      intro b inConceptValues
      have fiberEq :
          admitted.filter (fun x => concept x = b) =
            Finset.univ.filter (fun x =>
              concept x = b ∧
                target x = target (winner ⟨b, inConceptValues⟩)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨xInAdmitted, conceptX⟩
          refine ⟨conceptX, ?_⟩
          have selectedEq :
              (⟨concept x, concept_mem_values x⟩ : {b // b ∈ conceptValues}) =
                ⟨b, inConceptValues⟩ := Subtype.ext conceptX
          exact (Finset.mem_filter.mp xInAdmitted).2.trans
            (congrArg (fun value => target (winner value)) selectedEq)
        · rintro ⟨conceptX, targetX⟩
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_⟩, conceptX⟩
          have selectedEq :
              (⟨concept x, concept_mem_values x⟩ : {b // b ∈ conceptValues}) =
                ⟨b, inConceptValues⟩ := Subtype.ext conceptX
          exact targetX.trans
            (congrArg (fun value => target (winner value)) selectedEq).symm
      rw [fiberEq]
      exact (winnerMaximum ⟨b, inConceptValues⟩).symm

#print axioms maximum_factor_compatible_subdomain

end D5.S3.ConceptDynamics.TargetRisk.MaximumFactorCompatibleSubdomain
