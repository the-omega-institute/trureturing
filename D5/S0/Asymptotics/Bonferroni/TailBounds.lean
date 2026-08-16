/- GID: D5/S0/Asymptotics/Bonferroni/TailBounds
   generality: G
   mirror-B: D5/B/S0/Asymptotics/Bonferroni/TailBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Capture-count tails are bracketed by two consecutive binomial moments. -/

/- Library-search audit trail (2026-08-16):
   * Repository searches found the exact capture-count binomial-moment identity and the
     zero-capture Bonferroni truncation, but no positive capture-count tail bound.
   * Pinned Mathlib supplies `Nat.choose_pos` and `Nat.choose_succ_right_eq`; the latter is
     the exact adjacent-binomial relation needed for the lower coefficient.
   * Loogle returned `Nat.choose_succ_right_eq` as the only exact declaration match.
     LeanSearch returned no usable result for a binomial-moment tail-bound query.
   * The four decidable tables below validate the coefficient `k` before the general proof.
-/

import D5.S0.Asymptotics.WeightedProbability.BinomialMomentIdentity
import Mathlib.Tactic

open scoped BigOperators

namespace D5.S0.Asymptotics.Bonferroni.TailBounds

open D5.S0.Asymptotics.WeightedProbability.FiniteProductCapture
open D5.S0.Asymptotics.WeightedProbability.FiniteProductSetCapture
open D5.S0.Asymptotics.WeightedProbability.BinomialMomentIdentity

noncomputable section

variable {A Y : Type*}

local instance (priority := low) (p : Prop) : Decidable p := Classical.propDecidable p

-- For `|A| = 2` and `k = 1`, the actual indicator and the two-moment polynomial agree.
example :
    ((List.range 3).map fun n => if 1 <= n then (1 : Int) else 0,
      (List.range 3).map fun n => (Nat.choose n 1 : Int) - (Nat.choose n 2 : Int)) =
    ([0, 1, 1], [0, 1, 1]) := by decide

-- For `|A| = 2` and `k = 2`, both tables are `[0, 0, 1]`.
example :
    ((List.range 3).map fun n => if 2 <= n then (1 : Int) else 0,
      (List.range 3).map fun n =>
        (Nat.choose n 2 : Int) - 2 * (Nat.choose n 3 : Int)) =
    ([0, 0, 1], [0, 0, 1]) := by decide

-- For `|A| = 3` and `k = 1`, the lower polynomial differs only at the top count.
example :
    ((List.range 4).map fun n => if 1 <= n then (1 : Int) else 0,
      (List.range 4).map fun n => (Nat.choose n 1 : Int) - (Nat.choose n 2 : Int)) =
    ([0, 1, 1, 1], [0, 1, 1, 0]) := by decide

-- For `|A| = 3` and `k = 2`, the actual and lower-polynomial tables agree.
example :
    ((List.range 4).map fun n => if 2 <= n then (1 : Int) else 0,
      (List.range 4).map fun n =>
        (Nat.choose n 2 : Int) - 2 * (Nat.choose n 3 : Int)) =
    ([0, 0, 1, 1], [0, 0, 1, 1]) := by decide

/-- A capture-count tail is the disjoint sum of its exact-count masses. -/
theorem capture_count_tail_eq_sum_exact
    [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (f : Y -> Y) (k : Nat) :
    eventProbability q (fun s =>
        k <= ((Finset.univ : Finset A).filter fun a => Captured f s a).card) =
      ∑ j ∈ Finset.range (Fintype.card A + 1),
        if k <= j then
          eventProbability q (fun s =>
            ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j)
        else 0 := by
  classical
  let count := fun s : Sample A Y =>
    ((Finset.univ : Finset A).filter fun a => Captured f s a).card
  calc
    eventProbability q (fun s => k <= count s) =
        ∑ s : Sample A Y, if k <= count s then sampleWeight q s else 0 := by
      rfl
    _ = ∑ s : Sample A Y,
          ∑ j ∈ Finset.range (Fintype.card A + 1),
            if k <= j then
              if count s = j then sampleWeight q s else 0
            else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      have hcount_le : count s <= (Finset.univ : Finset A).card :=
        Finset.card_le_card (by simp)
      have hcount_mem : count s ∈ Finset.range (Fintype.card A + 1) := by
        rw [Finset.mem_range]
        simpa using Nat.lt_succ_of_le hcount_le
      rw [Finset.sum_eq_single (count s)]
      · simp
      · intro j hj hjne
        simp [Ne.symm hjne]
      · exact fun hnot => (hnot hcount_mem).elim
    _ = ∑ j ∈ Finset.range (Fintype.card A + 1),
          ∑ s : Sample A Y,
            if k <= j then
              if count s = j then sampleWeight q s else 0
            else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range (Fintype.card A + 1),
          if k <= j then
            eventProbability q (fun s => count s = j)
          else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hkj : k <= j
      · simp [hkj, eventProbability]
      · simp [hkj]

/-- The probability of at least `k` captures is bounded by the `k`-th binomial moment. -/
theorem capture_count_tail_le_binomial_moment
    [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real)
    (hq_nonneg : forall b y, 0 <= q b y)
    (f : Y -> Y) (k : Nat) :
    eventProbability q (fun s =>
        k <= ((Finset.univ : Finset A).filter fun a => Captured f s a).card)
      <= ∑ T ∈ (Finset.univ : Finset A).powersetCard k,
        setCaptureProbability q f T := by
  classical
  have hweight_nonneg (s : Sample A Y) : 0 <= sampleWeight q s := by
    rw [sampleWeight]
    apply mul_nonneg
    · exact Finset.prod_nonneg fun b hb => hq_nonneg b (s.1 b)
    · exact Finset.prod_nonneg fun a ha =>
        Finset.prod_nonneg fun b hb => hq_nonneg b.1 (s.2 a b)
  have hmass_nonneg (j : Nat) :
      0 <= eventProbability q (fun s =>
        ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j) := by
    rw [eventProbability]
    apply Finset.sum_nonneg
    intro s hs
    by_cases hcount :
        ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j
    · simp [hcount, hweight_nonneg s]
    · simp [hcount]
  rw [capture_count_tail_eq_sum_exact q f k,
    ← exact_capture_count_binomial_moment q f k]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hkj : k <= j
  · rw [if_pos hkj]
    have hchoose : (1 : Real) <= Nat.choose j k := by
      exact_mod_cast Nat.choose_pos hkj
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hchoose (hmass_nonneg j)
  · rw [if_neg hkj]
    exact mul_nonneg (Nat.cast_nonneg _) (hmass_nonneg j)

/-- The `k`-th moment minus `k` times the next moment bounds the `k`-tail from below. -/
theorem binomial_moment_sub_k_next_le_capture_count_tail
    [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real)
    (hq_nonneg : forall b y, 0 <= q b y)
    (f : Y -> Y) (k : Nat) :
    (∑ T ∈ (Finset.univ : Finset A).powersetCard k,
        setCaptureProbability q f T) -
      (k : Real) * ∑ T ∈ (Finset.univ : Finset A).powersetCard (k + 1),
        setCaptureProbability q f T <=
      eventProbability q (fun s =>
        k <= ((Finset.univ : Finset A).filter fun a => Captured f s a).card) := by
  classical
  have hweight_nonneg (s : Sample A Y) : 0 <= sampleWeight q s := by
    rw [sampleWeight]
    apply mul_nonneg
    · exact Finset.prod_nonneg fun b hb => hq_nonneg b (s.1 b)
    · exact Finset.prod_nonneg fun a ha =>
        Finset.prod_nonneg fun b hb => hq_nonneg b.1 (s.2 a b)
  have hmass_nonneg (j : Nat) :
      0 <= eventProbability q (fun s =>
        ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j) := by
    rw [eventProbability]
    apply Finset.sum_nonneg
    intro s hs
    by_cases hcount :
        ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j
    · simp [hcount, hweight_nonneg s]
    · simp [hcount]
  have hchoose (j : Nat) :
      (Nat.choose j k : Real) - (k : Real) * (Nat.choose j (k + 1) : Real) <=
        if k <= j then 1 else 0 := by
    by_cases hkzero : k = 0
    · subst k
      simp
    by_cases hj : k <= j
    · rw [if_pos hj]
      by_cases hjeq : j = k
      · subst j
        simp
      by_cases hjnext : j = k + 1
      · subst j
        simp [Nat.choose_succ_self_right]
      have hk : 1 <= k := Nat.one_le_iff_ne_zero.mpr hkzero
      have hgap : 2 <= j - k := by omega
      have hrelNat := Nat.choose_succ_right_eq j k
      have hrel :
          (Nat.choose j (k + 1) : Real) * ((k : Real) + 1) =
            (Nat.choose j k : Real) * (j - k : Nat) := by
        exact_mod_cast hrelNat
      have hkReal : (1 : Real) <= k := by exact_mod_cast hk
      have hgapReal : (2 : Real) <= (j - k : Nat) := by exact_mod_cast hgap
      have hcoeff :
          0 <= (k : Real) * (j - k : Nat) - ((k : Real) + 1) := by
        have hprod :
            0 <= ((k : Real) - 1) * (((j - k : Nat) : Real) - 1) :=
          mul_nonneg (sub_nonneg.mpr hkReal)
            (sub_nonneg.mpr (by linarith))
        nlinarith
      have hmul :
          0 <= ((k : Real) * (j - k : Nat) - ((k : Real) + 1)) *
            (Nat.choose j k : Real) :=
        mul_nonneg hcoeff (Nat.cast_nonneg _)
      have hscaled :
          ((k : Real) + 1) *
              ((Nat.choose j k : Real) -
                (k : Real) * (Nat.choose j (k + 1) : Real)) <= 0 := by
        calc
          ((k : Real) + 1) *
              ((Nat.choose j k : Real) -
                (k : Real) * (Nat.choose j (k + 1) : Real)) =
              ((k : Real) + 1) * (Nat.choose j k : Real) -
                (k : Real) *
                  ((Nat.choose j (k + 1) : Real) * ((k : Real) + 1)) := by ring
          _ = ((k : Real) + 1) * (Nat.choose j k : Real) -
                (k : Real) *
                  ((Nat.choose j k : Real) * (j - k : Nat)) := by rw [hrel]
          _ = -(((k : Real) * (j - k : Nat) - ((k : Real) + 1)) *
                (Nat.choose j k : Real)) := by ring
          _ <= 0 := neg_nonpos.mpr hmul
      have hnonpos :
          (Nat.choose j k : Real) -
              (k : Real) * (Nat.choose j (k + 1) : Real) <= 0 := by
        by_contra hnot
        have hpos :
            0 < (Nat.choose j k : Real) -
              (k : Real) * (Nat.choose j (k + 1) : Real) := lt_of_not_ge hnot
        have := mul_pos (show (0 : Real) < (k : Real) + 1 by positivity) hpos
        linarith
      linarith
    · have hjlt : j < k := Nat.lt_of_not_ge hj
      have hjlt' : j < k + 1 := by omega
      simp [if_neg hj, Nat.choose_eq_zero_of_lt hjlt,
        Nat.choose_eq_zero_of_lt hjlt']
  rw [← exact_capture_count_binomial_moment q f k,
    ← exact_capture_count_binomial_moment q f (k + 1),
    capture_count_tail_eq_sum_exact q f k]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j hj
  calc
    (Nat.choose j k : Real) * eventProbability q (fun s =>
          ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j) -
        (k : Real) * ((Nat.choose j (k + 1) : Real) *
          eventProbability q (fun s =>
            ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j)) =
      ((Nat.choose j k : Real) - (k : Real) * (Nat.choose j (k + 1) : Real)) *
        eventProbability q (fun s =>
          ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j) := by ring
    _ <= (if k <= j then 1 else 0) * eventProbability q (fun s =>
          ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j) :=
      mul_le_mul_of_nonneg_right (hchoose j) (hmass_nonneg j)
    _ = if k <= j then eventProbability q (fun s =>
          ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j) else 0 := by
      split <;> simp_all

#print axioms capture_count_tail_eq_sum_exact
#print axioms capture_count_tail_le_binomial_moment
#print axioms binomial_moment_sub_k_next_le_capture_count_tail

end

end D5.S0.Asymptotics.Bonferroni.TailBounds
