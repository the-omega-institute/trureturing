/- GID: D5/S3/Entropy/Observation/DualRepairEntropyDecomposition
   generality: G
   mirror-B: D5/B/S3/Entropy/Observation/DualRepairEntropyDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Conditional entropy across canonical interior and closure repairs decomposes exactly. -/

/- Library-search audit trail (2026-09-02):
   * Repository body-shape searches found the canonical `congruenceInterior`,
     `congruenceClosure`, `pushforward`, and quotient-fiber entropy decomposition;
     all are imported and used directly below.
   * The closest repository chain rule is the generic three-coordinate theorem
     `conditional_choice_outcome_chain_rule`. It is not an exact hit for the
     canonical repair quotients, and no frozen theorem states the equality below.
   * Pinned Mathlib and the other installed Lean packages contain no finite
     real-valued conditional-entropy definition or matching repair decomposition. -/

import D5.S3.Entropy.Fusion.QuotientFiberDecomposition
import D5.S3.Observer.Separation.CongruenceClosureDuality

namespace D5.S3.Entropy.Observation.DualRepairEntropyDecomposition

open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.Fusion.QuotientFiberDecomposition
open D5.S3.Entropy.MaxEntropy
open D5.S3.Observer.Separation.CongruenceClosureDuality
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- For a finite full-support law, the conditional entropy between the predictive
interior and forgetting closure is the sum of the two canonical repair costs. -/
theorem dual_repair_entropy_decomposition
    {X : Type*} [Fintype X]
    (update : X -> X) (relation : Setoid X) (mass : X -> Real)
    (hmass : (forall x, 0 < mass x) /\ ∑ x, mass x = 1) :
    letI : Fintype (Quotient (congruenceInterior update relation)) :=
      Fintype.ofFinite _
    letI : Fintype (Quotient relation) := Fintype.ofFinite _
    letI : Fintype (Quotient (congruenceClosure update relation)) :=
      Fintype.ofFinite _
    let interiorToRelation :
        Quotient (congruenceInterior update relation) -> Quotient relation :=
      Quotient.map id (by
        intro x y hxy
        exact (dual_congruence_repair_laws update).1 relation hxy)
    let relationToClosure :
        Quotient relation -> Quotient (congruenceClosure update relation) :=
      Quotient.map id (by
        intro x y hxy
        exact (dual_congruence_repair_laws update).2.2.2.1 relation hxy)
    let interiorLaw : Quotient (congruenceInterior update relation) -> Real :=
      pushforward (Quotient.mk (congruenceInterior update relation)) mass
    let relationLaw : Quotient relation -> Real :=
      pushforward interiorToRelation interiorLaw
    conditionalEntropy
        (pushforward
          (fun interiorClass =>
            (relationToClosure (interiorToRelation interiorClass), interiorClass))
          interiorLaw) =
      conditionalEntropy
          (pushforward
            (fun relationClass => (relationToClosure relationClass, relationClass))
            relationLaw) +
        conditionalEntropy
          (pushforward
            (fun interiorClass => (interiorToRelation interiorClass, interiorClass))
            interiorLaw) := by
  classical
  dsimp only
  letI interiorFintype :
      Fintype (Quotient (congruenceInterior update relation)) :=
    Fintype.ofFinite _
  letI relationFintype : Fintype (Quotient relation) := Fintype.ofFinite _
  letI closureFintype :
      Fintype (Quotient (congruenceClosure update relation)) :=
    Fintype.ofFinite _
  let interiorToRelation :
      Quotient (congruenceInterior update relation) -> Quotient relation :=
    Quotient.map id (by
      intro x y hxy
      exact (dual_congruence_repair_laws update).1 relation hxy)
  let relationToClosure :
      Quotient relation -> Quotient (congruenceClosure update relation) :=
    Quotient.map id (by
      intro x y hxy
      exact (dual_congruence_repair_laws update).2.2.2.1 relation hxy)
  let interiorLaw : Quotient (congruenceInterior update relation) -> Real :=
    pushforward (Quotient.mk (congruenceInterior update relation)) mass
  let relationLaw : Quotient relation -> Real :=
    pushforward interiorToRelation interiorLaw
  change conditionalEntropy
      (pushforward
        (fun interiorClass =>
          (relationToClosure (interiorToRelation interiorClass), interiorClass))
        interiorLaw) =
    conditionalEntropy
        (pushforward
          (fun relationClass => (relationToClosure relationClass, relationClass))
          relationLaw) +
      conditionalEntropy
        (pushforward
          (fun interiorClass => (interiorToRelation interiorClass, interiorClass))
          interiorLaw)
  have interiorLawNonnegative : forall interiorClass, 0 <= interiorLaw interiorClass := by
    intro interiorClass
    simp only [interiorLaw, pushforward]
    exact Finset.sum_nonneg fun x _ => by
      by_cases hclass :
          Quotient.mk (congruenceInterior update relation) x = interiorClass
      · simp [hclass, (hmass.1 x).le]
      · simp [hclass]
  have interiorLawTotal : ∑ interiorClass, interiorLaw interiorClass = 1 := by
    simp only [interiorLaw, pushforward]
    rw [Finset.sum_comm]
    calc
      _ = ∑ x, mass x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_eq_single
          (Quotient.mk (congruenceInterior update relation) x)]
        · simp
        · intro interiorClass _ hne
          simp [Ne.symm hne]
        · simp
      _ = 1 := hmass.2
  have relationLawNonnegative : forall relationClass, 0 <= relationLaw relationClass := by
    intro relationClass
    simp only [relationLaw, pushforward]
    exact Finset.sum_nonneg fun interiorClass _ => by
      by_cases hclass : interiorToRelation interiorClass = relationClass
      · simp [hclass, interiorLawNonnegative interiorClass]
      · simp [hclass]
  have relationLawTotal : ∑ relationClass, relationLaw relationClass = 1 := by
    simp only [relationLaw, pushforward]
    rw [Finset.sum_comm]
    calc
      _ = ∑ interiorClass, interiorLaw interiorClass := by
        apply Finset.sum_congr rfl
        intro interiorClass _
        rw [Finset.sum_eq_single (interiorToRelation interiorClass)]
        · simp
        · intro relationClass _ hne
          simp [Ne.symm hne]
        · simp
      _ = 1 := interiorLawTotal
  have nameBalance :=
    (quotient_fiber_entropy_decomposition interiorLaw
      (relationToClosure ∘ interiorToRelation)
      interiorLawNonnegative interiorLawTotal).2
  have predictionBalance :=
    (quotient_fiber_entropy_decomposition interiorLaw interiorToRelation
      interiorLawNonnegative interiorLawTotal).2
  have forgettingBalance :=
    (quotient_fiber_entropy_decomposition relationLaw relationToClosure
      relationLawNonnegative relationLawTotal).2
  rw [show pushforward relationToClosure relationLaw =
      pushforward (relationToClosure ∘ interiorToRelation) interiorLaw by
    simp only [relationLaw]
    funext c
    simp only [pushforward]
    calc
      _ = ∑ relationClass, ∑ interiorClass,
            if relationToClosure relationClass = c then
              (if interiorToRelation interiorClass = relationClass
                then interiorLaw interiorClass else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro relationClass _
        by_cases hclass : relationToClosure relationClass = c
        · simp only [if_pos hclass]
          apply Finset.sum_congr rfl
          intro interiorClass _
          by_cases hinner : interiorToRelation interiorClass = relationClass
          · simp [hinner]
          · simp [hinner]
        · simp [hclass]
      _ = ∑ interiorClass, ∑ relationClass,
          if relationToClosure relationClass = c then
            (if interiorToRelation interiorClass = relationClass
              then interiorLaw interiorClass else 0) else 0 :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro interiorClass _
        rw [Finset.sum_eq_single (interiorToRelation interiorClass)]
        · simp
        · intro relationClass _ hne
          simp [Ne.symm hne]
        · simp] at forgettingBalance
  simp only [Function.comp_apply] at nameBalance
  change shannonEntropy interiorLaw =
    shannonEntropy relationLaw +
      conditionalEntropy
        (pushforward
          (fun interiorClass => (interiorToRelation interiorClass, interiorClass))
          interiorLaw) at predictionBalance
  linarith

#print axioms dual_repair_entropy_decomposition

end D5.S3.Entropy.Observation.DualRepairEntropyDecomposition
