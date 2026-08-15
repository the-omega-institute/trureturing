/- GID: D5/S0/Asymptotics/WeightedProbability/SecondMomentCoherence
   generality: G
   mirror-B: D5/B/S0/Asymptotics/WeightedProbability/SecondMomentCoherence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The exact capture-count masses reproduce their independently frozen second moment. -/

/- Library-search audit trail (2026-08-16):
   * Repository searches found the frozen exact count distribution and the frozen
     indicator-square second moment, but no coherence theorem linking the two.
   * Pinned Mathlib supplies `Finset.sum_eq_single` for the unique realized count and
     `Finset.sum_boole` for identifying the cardinality with its real-valued indicator sum.
   * The result rewrites the explicit alternating product mass through the frozen
     `exact_capture_count_probability`, then applies the independently frozen
     `capture_count_second_moment_and_variance`.
-/

import D5.S0.Asymptotics.WeightedProbability.CaptureCountCoherence
import D5.S0.Diagonal.Probability.CaptureCountMoments

open scoped BigOperators

namespace D5.S0.Asymptotics.WeightedProbability.SecondMomentCoherence

open ExactCaptureCount
open FiniteBonferroni
open FiniteProductCapture
open FiniteProductSetCapture
open D5.S0.Diagonal.Probability.CaptureSecondMoment
open D5.S0.Diagonal.Probability.CaptureCountMoments

noncomputable section

variable {A Y : Type*}

local instance (priority := low) (p : Prop) : Decidable p := Classical.propDecidable p

/-- The second moment of the explicit distribution agrees with the independently frozen
indicator-square calculation of the capture count. -/
theorem exact_capture_count_probability_second_moment_agreement
    [Fintype A] [Fintype Y] [DecidableEq A] [LinearOrder A]
    (q : A -> Y -> Real)
    (hq_nonneg : forall b y, 0 <= q b y)
    (hq_sum : forall b, ∑ y, q b y = 1)
    (f : Y -> Y) :
    (∑ j ∈ Finset.range (Fintype.card A + 1),
        (j : Real) ^ 2 *
          ∑ S ∈ (Finset.univ : Finset A).powersetCard j,
            ∑ U ∈ ((Finset.univ : Finset A) \ S).powerset,
              (-1 : Real) ^ U.card *
                ∏ b, if b ∈ S ∪ U then
                  fixedPowerMass q f b (S ∪ U).card
                else collisionPowerMass q f b (S ∪ U).card) =
        (∑ a, captureProbability q f a) + 2 * pairProbabilitySum q f := by
  rename_i fintypeA fintypeY decidableEqA linearOrderA
  have hdecidableEq : decidableEqA = LinearOrder.toDecidableEq :=
    Subsingleton.elim _ _
  rw [hdecidableEq]
  letI : DecidableEq A := LinearOrder.toDecidableEq
  simp_rw [← exact_capture_count_probability q hq_sum f]
  calc
    (∑ j ∈ Finset.range (Fintype.card A + 1),
        (j : Real) ^ 2 * eventProbability q (fun s =>
          ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j)) =
      ∑ s : Sample A Y, sampleWeight q s *
          (∑ a, if Captured f s a then 1 else 0) ^ 2 := by
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
        rw [if_pos (by rfl)]
      · intro j hj hjC
        simp [C, Ne.symm hjC]
      · exact fun hCnot => (hCnot hcard_mem).elim
    _ = (∑ a, captureProbability q f a) + 2 * pairProbabilitySum q f := by
      simpa only using
        (capture_count_second_moment_and_variance q hq_nonneg hq_sum f).1

/- The normalization hypotheses and both finite domains are simultaneously inhabited. -/
example :
    let q : Fin 1 -> Unit -> Real := fun _ _ => 1
    (forall b y, 0 <= q b y) ∧ (forall b, ∑ y, q b y = 1) := by
  simp

#print axioms exact_capture_count_probability_second_moment_agreement

end

end D5.S0.Asymptotics.WeightedProbability.SecondMomentCoherence
