/- GID: D5/S0/Diagonal/Probability/CaptureSecondMoment
   generality: G
   mirror-B: D5/B/S0/Diagonal/Probability/CaptureSecondMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The capture count has its exact variance identity and a second-moment lower bound. -/

/- Library-search audit trail (2026-08-15):
   * Repository searches for `variance`, `second moment`, `Paley`, and `Chebyshev` under
     `D5/S0/Diagonal` and `D5/S0/Asymptotics` returned no declaration. The private indicator
     calculations in `FiniteBonferroni` prove different first- and second-order union bounds.
   * Pinned Mathlib contains finite Cauchy--Schwarz as
     `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul`, but no Paley--Zygmund theorem.
   * The count below uses the frozen `FiniteProductCapture.Captured` predicate directly. No
     second capture event or probability model is introduced.
-/

import D5.S0.Asymptotics.WeightedProbability.FiniteProductCapture
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open scoped BigOperators

namespace D5.S0.Diagonal.Probability.CaptureSecondMoment

open D5.S0.Asymptotics.WeightedProbability.FiniteProductCapture

noncomputable section

variable {A Y : Type*}

local instance (priority := low) (p : Prop) : Decidable p := Classical.propDecidable p

/-- In the normalized finite listing model, the mean capture count is the sum of the frozen
one-address capture probabilities, its centered variance is the second moment minus the square
of the mean, and the probability of at least one frozen `Captured` event satisfies the
Paley--Zygmund second-moment lower bound. -/
theorem capture_count_variance_and_lower_bound
    [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real)
    (hq_nonneg : forall b y, 0 <= q b y)
    (hq_sum : forall b, ∑ y, q b y = 1)
    (f : Y -> Y) :
    let count : Sample A Y -> Real := fun s =>
      ∑ a, if Captured f s a then 1 else 0
    let mean := ∑ s, sampleWeight q s * count s
    let secondMoment := ∑ s, sampleWeight q s * count s ^ 2
    let variance := ∑ s, sampleWeight q s * (count s - mean) ^ 2
    mean = ∑ a, captureProbability q f a ∧
      variance = secondMoment - mean ^ 2 ∧
      (0 < secondMoment ->
        mean ^ 2 / secondMoment <=
          eventProbability q (fun s => exists a, Captured f s a)) := by
  classical
  let count : Sample A Y -> Real := fun s =>
    ∑ a, if Captured f s a then 1 else 0
  let mean := ∑ s, sampleWeight q s * count s
  let secondMoment := ∑ s, sampleWeight q s * count s ^ 2
  let variance := ∑ s, sampleWeight q s * (count s - mean) ^ 2
  change mean = ∑ a, captureProbability q f a ∧
    variance = secondMoment - mean ^ 2 ∧
    (0 < secondMoment ->
      mean ^ 2 / secondMoment <=
        eventProbability q (fun s => exists a, Captured f s a))
  have sampleWeight_nonneg (s : Sample A Y) : 0 <= sampleWeight q s := by
    rw [sampleWeight]
    exact mul_nonneg
      (Finset.prod_nonneg fun b _ => hq_nonneg b (s.1 b))
      (Finset.prod_nonneg fun a _ =>
        Finset.prod_nonneg fun b _ => hq_nonneg b.1 (s.2 a b))
  have hmean : mean = ∑ a, captureProbability q f a := by
    dsimp [mean, count]
    calc
      (∑ s : Sample A Y,
          sampleWeight q s * ∑ a, if Captured f s a then 1 else 0) =
          ∑ s : Sample A Y, ∑ a,
            if Captured f s a then sampleWeight q s else 0 := by
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : Captured f s a <;> simp [h]
      _ = ∑ a, ∑ s : Sample A Y,
          if Captured f s a then sampleWeight q s else 0 := Finset.sum_comm
      _ = ∑ a, captureProbability q f a := by
        simp only [captureProbability, eventProbability]
  have hvariance : variance = secondMoment - mean ^ 2 := by
    have htotal : (∑ s : Sample A Y, sampleWeight q s) = 1 :=
      sample_weight_sum_one q hq_sum
    dsimp [variance, secondMoment]
    calc
      (∑ s : Sample A Y, sampleWeight q s * (count s - mean) ^ 2) =
          ∑ s : Sample A Y,
            (sampleWeight q s * count s ^ 2 -
              (2 * mean) * (sampleWeight q s * count s) +
              mean ^ 2 * sampleWeight q s) := by
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = (∑ s : Sample A Y, sampleWeight q s * count s ^ 2) -
          (2 * mean) * (∑ s : Sample A Y, sampleWeight q s * count s) +
          mean ^ 2 * ∑ s : Sample A Y, sampleWeight q s := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
      _ = (∑ s : Sample A Y, sampleWeight q s * count s ^ 2) - mean ^ 2 := by
        rw [show (∑ s : Sample A Y, sampleWeight q s * count s) = mean by rfl,
          htotal]
        ring
  have hsecondMoment :
      mean ^ 2 <= secondMoment *
        eventProbability q (fun s => exists a, Captured f s a) := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (s := Finset.univ)
      (r := fun s : Sample A Y => sampleWeight q s * count s)
      (f := fun s : Sample A Y => sampleWeight q s * count s ^ 2)
      (g := fun s : Sample A Y =>
        if exists a, Captured f s a then sampleWeight q s else 0)
      (fun s _ => mul_nonneg (sampleWeight_nonneg s) (sq_nonneg (count s)))
      (fun s _ => by
        by_cases h : exists a, Captured f s a <;> simp [h, sampleWeight_nonneg s])
      (fun s _ => by
        by_cases h : exists a, Captured f s a
        · simp only [h, if_true]
          exact le_of_eq (by ring)
        · have hcount : count s = 0 := by
            dsimp [count]
            apply Finset.sum_eq_zero
            intro a _
            simp [not_exists.mp h a]
          simp [h, hcount])
    simpa only [Finset.sum_filter, Finset.mem_univ, true_and,
      eventProbability] using hcs
  refine ⟨hmean, hvariance, fun hpos => ?_⟩
  exact (div_le_iff₀ hpos).2 (by simpa [mul_comm] using hsecondMoment)

/- The hypotheses and both finite domains are simultaneously inhabited. -/
example :
    let q : Fin 1 -> Unit -> Real := fun _ _ => 1
    (forall b y, 0 <= q b y) ∧ (forall b, ∑ y, q b y = 1) := by
  simp

/- The frozen independent-listing sample domain used by the theorem is inhabited. -/
example : Sample (Fin 1) Unit := ⟨fun _ => (), fun _ _ => ()⟩

#print axioms capture_count_variance_and_lower_bound

end

end D5.S0.Diagonal.Probability.CaptureSecondMoment
