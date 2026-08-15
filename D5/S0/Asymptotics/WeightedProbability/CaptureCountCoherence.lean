/- GID: D5/S0/Asymptotics/WeightedProbability/CaptureCountCoherence
   generality: G
   mirror-B: D5/B/S0/Asymptotics/WeightedProbability/CaptureCountCoherence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The exact capture-count masses normalize and reproduce their first moment. -/

/- Library-search audit trail (2026-08-16):
   * Repository searches found the frozen exact count distribution, total sample-mass law, and
     capture-count first moment, but no normalization or distribution-to-moment coherence theorem.
   * Pinned Mathlib supplies `Finset.sum_eq_single` for the unique realized count and
     `Finset.sum_boole` for identifying the cardinality with its real-valued indicator sum.
   * Both results below rewrite the explicit alternating product mass through the frozen
     `exact_capture_count_probability`; the mean result then applies the independent frozen
     `capture_count_variance_and_lower_bound` route.
-/

import D5.S0.Asymptotics.WeightedProbability.ExactCaptureCount
import D5.S0.Diagonal.Probability.CaptureSecondMoment

open scoped BigOperators

namespace D5.S0.Asymptotics.WeightedProbability.CaptureCountCoherence

open ExactCaptureCount
open FiniteProductCapture
open FiniteProductSetCapture
open D5.S0.Diagonal.Probability.CaptureSecondMoment

noncomputable section

variable {A Y : Type*}

local instance (priority := low) (p : Prop) : Decidable p := Classical.propDecidable p

/-- Summing the explicit alternating product mass over every possible capture count gives one. -/
theorem exact_capture_count_probability_normalizes
    [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (hq : forall b, ∑ y, q b y = 1)
    (f : Y -> Y) :
    (∑ j ∈ Finset.range (Fintype.card A + 1),
        ∑ S ∈ (Finset.univ : Finset A).powersetCard j,
          ∑ U ∈ ((Finset.univ : Finset A) \ S).powerset,
            (-1 : Real) ^ U.card *
              ∏ b, if b ∈ S ∪ U then
                fixedPowerMass q f b (S ∪ U).card
              else collisionPowerMass q f b (S ∪ U).card) = 1 := by
  classical
  simp_rw [← exact_capture_count_probability q hq f]
  simp only [eventProbability]
  rw [Finset.sum_comm]
  calc
    (∑ s : Sample A Y,
        ∑ j ∈ Finset.range (Fintype.card A + 1),
          if ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j then
            sampleWeight q s
          else 0) =
        ∑ s : Sample A Y, sampleWeight q s := by
      apply Finset.sum_congr rfl
      intro s _
      let C := (Finset.univ : Finset A).filter fun a => Captured f s a
      have hcard_le : C.card ≤ (Finset.univ : Finset A).card :=
        Finset.card_le_card (by simp [C])
      have hcard_mem : C.card ∈ Finset.range (Fintype.card A + 1) := by
        rw [Finset.mem_range]
        simpa using Nat.lt_succ_of_le hcard_le
      rw [Finset.sum_eq_single C.card]
      · simp [C]
      · intro j hj hjC
        simp [C, Ne.symm hjC]
      · exact fun hCnot => (hCnot hcard_mem).elim
    _ = 1 := sample_weight_sum_one q hq

/-- The first moment of the explicit distribution agrees with the frozen indicator-linearity
calculation of the mean capture count. -/
theorem exact_capture_count_probability_mean_agreement
    [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real)
    (hq_nonneg : forall b y, 0 <= q b y)
    (hq_sum : forall b, ∑ y, q b y = 1)
    (f : Y -> Y) :
    (∑ j ∈ Finset.range (Fintype.card A + 1),
        (j : Real) *
          ∑ S ∈ (Finset.univ : Finset A).powersetCard j,
            ∑ U ∈ ((Finset.univ : Finset A) \ S).powerset,
              (-1 : Real) ^ U.card *
                ∏ b, if b ∈ S ∪ U then
                  fixedPowerMass q f b (S ∪ U).card
                else collisionPowerMass q f b (S ∪ U).card) =
        ∑ a, captureProbability q f a := by
  classical
  simp_rw [← exact_capture_count_probability q hq_sum f]
  calc
    (∑ j ∈ Finset.range (Fintype.card A + 1),
        (j : Real) * eventProbability q (fun s =>
          ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j)) =
      ∑ s : Sample A Y, sampleWeight q s *
          ∑ a, if Captured f s a then 1 else 0 := by
      simp only [eventProbability]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      let C := (Finset.univ : Finset A).filter fun a => Captured f s a
      have hcard_le : C.card ≤ (Finset.univ : Finset A).card :=
        Finset.card_le_card (by simp [C])
      have hcard_mem : C.card ∈ Finset.range (Fintype.card A + 1) := by
        rw [Finset.mem_range]
        simpa using Nat.lt_succ_of_le hcard_le
      have hcount : (C.card : Real) =
          ∑ a, if Captured f s a then 1 else 0 := by
        simp [C]
      rw [Finset.sum_eq_single C.card]
      · rw [hcount, mul_comm]
        rw [if_pos (by rfl), Finset.mul_sum]
      · intro j hj hjC
        simp [C, Ne.symm hjC]
      · exact fun hCnot => (hCnot hcard_mem).elim
    _ = ∑ a, captureProbability q f a := by
      exact (capture_count_variance_and_lower_bound q hq_nonneg hq_sum f).1

/- The normalization hypotheses and both finite domains are simultaneously inhabited. -/
example :
    let q : Fin 1 -> Unit -> Real := fun _ _ => 1
    (forall b y, 0 <= q b y) ∧ (forall b, ∑ y, q b y = 1) := by
  simp

/- The frozen independent-listing sample domain used by both theorems is inhabited. -/
example : Sample (Fin 1) Unit := ⟨fun _ => (), fun _ _ => ()⟩

#print axioms exact_capture_count_probability_normalizes
#print axioms exact_capture_count_probability_mean_agreement

end

end D5.S0.Asymptotics.WeightedProbability.CaptureCountCoherence
