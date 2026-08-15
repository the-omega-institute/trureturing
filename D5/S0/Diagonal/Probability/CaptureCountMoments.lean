/- GID: D5/S0/Diagonal/Probability/CaptureCountMoments
   generality: G
   mirror-B: D5/B/S0/Diagonal/Probability/CaptureCountMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Capture-count second moments and variance are exact one- and two-address sums. -/

/- Library-search audit trail (2026-08-16):
   * Repository searches found the frozen mean/variance/lower-bound theorem in
     `Diagonal/Probability/CaptureSecondMoment` and the unordered pair sum in
     `Asymptotics/WeightedProbability/FiniteBonferroni`, but no exact expansion of the
     capture-count second moment into one- and two-address probabilities.
   * Pinned Mathlib supplies `Fintype.sum_mul_sum` and `Finset.mul_sum` for rearranging the
     finite indicator products, but no theorem matching this capture-count identity.
   * The expectation identity is not redeclared: the proof applies the frozen theorem and
     evaluates only its previously abstract second-moment term.
-/

import D5.S0.Diagonal.Probability.CaptureSecondMoment
import D5.S0.Asymptotics.WeightedProbability.FiniteBonferroni

open scoped BigOperators

namespace D5.S0.Diagonal.Probability.CaptureCountMoments

open D5.S0.Asymptotics.WeightedProbability.FiniteProductCapture
open D5.S0.Asymptotics.WeightedProbability.FiniteBonferroni
open D5.S0.Diagonal.Probability.CaptureSecondMoment

noncomputable section

variable {A Y : Type*}

local instance (priority := low) (p : Prop) : Decidable p := Classical.propDecidable p

/-- The second moment of the frozen finite capture count is the one-address probability sum
plus twice the unordered two-address probability sum. Consequently its centered variance has
the same exact expansion minus the square of the already-frozen mean. -/
theorem capture_count_second_moment_and_variance
    [Fintype A] [Fintype Y] [LinearOrder A]
    (q : A -> Y -> Real)
    (hq_nonneg : forall b y, 0 <= q b y)
    (hq_sum : forall b, ∑ y, q b y = 1)
    (f : Y -> Y) :
    let count : Sample A Y -> Real := fun s =>
      ∑ a, if Captured f s a then 1 else 0
    let mean := ∑ s, sampleWeight q s * count s
    let secondMoment := ∑ s, sampleWeight q s * count s ^ 2
    let variance := ∑ s, sampleWeight q s * (count s - mean) ^ 2
    secondMoment =
        (∑ a, captureProbability q f a) + 2 * pairProbabilitySum q f ∧
      variance =
        (∑ a, captureProbability q f a) + 2 * pairProbabilitySum q f -
          (∑ a, captureProbability q f a) ^ 2 := by
  classical
  let count : Sample A Y -> Real := fun s =>
    ∑ a, if Captured f s a then 1 else 0
  let mean := ∑ s, sampleWeight q s * count s
  let secondMoment := ∑ s, sampleWeight q s * count s ^ 2
  let variance := ∑ s, sampleWeight q s * (count s - mean) ^ 2
  change secondMoment =
      (∑ a, captureProbability q f a) + 2 * pairProbabilitySum q f ∧
    variance =
      (∑ a, captureProbability q f a) + 2 * pairProbabilitySum q f -
        (∑ a, captureProbability q f a) ^ 2
  have hbase := capture_count_variance_and_lower_bound q hq_nonneg hq_sum f
  change mean = ∑ a, captureProbability q f a ∧
    variance = secondMoment - mean ^ 2 ∧ _ at hbase
  have hmean := hbase.1
  have hvariance := hbase.2.1
  let singleIndicator (s : Sample A Y) (S : Finset A) : Real :=
    ∑ a ∈ S, if Captured f s a then 1 else 0
  let pairIndicator (s : Sample A Y) (S : Finset A) : Real :=
    ∑ a ∈ S, ∑ a' ∈ S,
      if a < a' ∧ Captured f s a ∧ Captured f s a' then 1 else 0
  have singleIndicator_insert (s : Sample A Y) (S : Finset A) (a : A)
      (ha : a ∉ S) :
      singleIndicator s (insert a S) =
        (if Captured f s a then 1 else 0) + singleIndicator s S := by
    simp only [singleIndicator]
    rw [Finset.sum_insert ha]
  have pairIndicator_insert (s : Sample A Y) (S : Finset A) (a : A)
      (ha : a ∉ S) :
      pairIndicator s (insert a S) =
        pairIndicator s S +
          (if Captured f s a then 1 else 0) * singleIndicator s S := by
    simp only [pairIndicator, singleIndicator]
    simp_rw [Finset.sum_insert ha]
    have hcross :
        (∑ b ∈ S,
            if a < b ∧ Captured f s a ∧ Captured f s b then (1 : Real) else 0) +
          (∑ b ∈ S,
            if b < a ∧ Captured f s b ∧ Captured f s a then (1 : Real) else 0) =
        (if Captured f s a then 1 else 0) *
          ∑ b ∈ S, if Captured f s b then (1 : Real) else 0 := by
      by_cases hPa : Captured f s a
      · simp only [hPa, and_true, true_and, if_true, one_mul]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro b hb
        have hba : b ≠ a := by
          intro h
          subst b
          exact ha hb
        rcases lt_or_gt_of_ne hba with hlt | hgt
        · simp [hlt, not_lt_of_ge hlt.le]
        · simp [hgt, not_lt_of_ge hgt.le]
      · simp [hPa]
    simp only [lt_irrefl, false_and, if_false, zero_add]
    rw [Finset.sum_add_distrib, ← add_assoc, hcross]
    ring
  have singleIndicator_sq (s : Sample A Y) (S : Finset A) :
      singleIndicator s S ^ 2 =
        singleIndicator s S + 2 * pairIndicator s S := by
    induction S using Finset.induction with
    | empty => simp [singleIndicator, pairIndicator]
    | @insert a S ha ih =>
        rw [singleIndicator_insert s S a ha, pairIndicator_insert s S a ha]
        by_cases hPa : Captured f s a
        · simp only [hPa, if_true]
          nlinarith
        · simp [hPa, ih]
  have hpair :
      pairProbabilitySum q f =
        ∑ s : Sample A Y,
          sampleWeight q s * pairIndicator s Finset.univ := by
    simp only [pairIndicator]
    calc
      pairProbabilitySum q f =
          ∑ a, ∑ a', ∑ s : Sample A Y,
            if a < a' ∧ Captured f s a ∧ Captured f s a' then
              sampleWeight q s else 0 := by
        simp only [pairProbabilitySum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro a' _
        by_cases haa' : a < a' <;>
          simp [haa', pairCaptureProbability, eventProbability]
      _ = ∑ a, ∑ s : Sample A Y, ∑ a',
          if a < a' ∧ Captured f s a ∧ Captured f s a' then
            sampleWeight q s else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      _ = ∑ s : Sample A Y, ∑ a, ∑ a',
          if a < a' ∧ Captured f s a ∧ Captured f s a' then
            sampleWeight q s else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a' _
        by_cases h : a < a' ∧ Captured f s a ∧ Captured f s a' <;> simp [h]
  have hsecond :
      secondMoment =
        (∑ a, captureProbability q f a) + 2 * pairProbabilitySum q f := by
    dsimp [secondMoment]
    calc
      (∑ s : Sample A Y, sampleWeight q s * count s ^ 2) =
          ∑ s : Sample A Y,
            sampleWeight q s *
              (count s + 2 * pairIndicator s Finset.univ) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [show count s = singleIndicator s Finset.univ by
          simp [count, singleIndicator]]
        rw [singleIndicator_sq]
      _ = mean + 2 * ∑ s : Sample A Y,
          sampleWeight q s * pairIndicator s Finset.univ := by
        dsimp [mean]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = (∑ a, captureProbability q f a) +
          2 * pairProbabilitySum q f := by rw [hmean, hpair]
  refine ⟨hsecond, ?_⟩
  calc
    variance = secondMoment - mean ^ 2 := hvariance
    _ = (∑ a, captureProbability q f a) + 2 * pairProbabilitySum q f -
        (∑ a, captureProbability q f a) ^ 2 := by rw [hsecond, hmean]

/- The normalization hypotheses and both finite domains are simultaneously inhabited. -/
example :
    let q : Fin 1 -> Unit -> Real := fun _ _ => 1
    (forall b y, 0 <= q b y) ∧ (forall b, ∑ y, q b y = 1) := by
  simp

/- The frozen independent-listing sample domain used by the theorem is inhabited. -/
example : Sample (Fin 1) Unit := ⟨fun _ => (), fun _ _ => ()⟩

#print axioms capture_count_second_moment_and_variance

end

end D5.S0.Diagonal.Probability.CaptureCountMoments
