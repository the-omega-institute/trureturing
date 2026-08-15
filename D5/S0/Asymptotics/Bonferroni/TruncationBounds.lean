/- GID: D5/S0/Asymptotics/Bonferroni/TruncationBounds
   generality: G
   mirror-B: D5/B/S0/Asymptotics/Bonferroni/TruncationBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every alternating capture truncation bounds escape according to its parity. -/

/- Library-search audit trail (2026-08-16):
   * Loogle and LeanSearch both returned
     `Int.alternating_sum_range_choose_eq_choose` from
     `Mathlib.Data.Nat.Choose.Sum` for the required partial alternating binomial sum.
   * Repository searches found only the degree-one and degree-two bounds in
     `FiniteBonferroni`; no arbitrary-order truncation theorem was present.
   * The proof reuses `exact_capture_count_binomial_moment` to exchange each
     prescribed-set capture sum for the corresponding capture-count moment.
-/

import D5.S0.Asymptotics.WeightedProbability.BinomialMomentIdentity
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open scoped BigOperators

namespace D5.S0.Asymptotics.Bonferroni.TruncationBounds

open D5.S0.Asymptotics.WeightedProbability.FiniteProductCapture
open D5.S0.Asymptotics.WeightedProbability.FiniteProductSetCapture
open D5.S0.Asymptotics.WeightedProbability.FiniteBonferroni
open D5.S0.Asymptotics.WeightedProbability.BinomialMomentIdentity

noncomputable section

variable {A Y : Type*}

local instance (priority := low) (p : Prop) : Decidable p := Classical.propDecidable p

/-- Even truncations bound escape from above and odd truncations bound it from below. -/
theorem escape_bonferroni_truncation
    [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real)
    (hq_nonneg : forall b y, 0 <= q b y)
    (f : Y -> Y) (m : Nat) :
    (Even m ->
        escapeProbability q f <=
          ∑ r ∈ Finset.range (m + 1), (-1 : Real) ^ r *
            ∑ T ∈ (Finset.univ : Finset A).powersetCard r,
              setCaptureProbability q f T) ∧
    (Odd m ->
        ∑ r ∈ Finset.range (m + 1), (-1 : Real) ^ r *
            ∑ T ∈ (Finset.univ : Finset A).powersetCard r,
              setCaptureProbability q f T
          <= escapeProbability q f) := by
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
  have hpartial_zero :
      (∑ r ∈ Finset.range (m + 1),
          (-1 : Real) ^ r * (Nat.choose 0 r : Real)) = 1 := by
    induction m with
    | zero => simp
    | succ m ih =>
        simp [Finset.sum_range_succ, ih]
  have hpartial (j : Nat) (hj : j ≠ 0) :
      (∑ r ∈ Finset.range (m + 1),
          (-1 : Real) ^ r * (Nat.choose j r : Real)) =
        (-1 : Real) ^ m * (Nat.choose (j - 1) m : Real) := by
    have hsucc : j - 1 + 1 = j := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj)
    have hint := Int.alternating_sum_range_choose_eq_choose
      (n := j - 1) (m := m)
    rw [hsucc] at hint
    exact_mod_cast hint
  have htruncation :
      (∑ r ∈ Finset.range (m + 1), (-1 : Real) ^ r *
          ∑ T ∈ (Finset.univ : Finset A).powersetCard r,
            setCaptureProbability q f T) =
        ∑ j ∈ Finset.range (Fintype.card A + 1),
          (∑ r ∈ Finset.range (m + 1),
            (-1 : Real) ^ r * (Nat.choose j r : Real)) *
              eventProbability q (fun s =>
                ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j) := by
    calc
      (∑ r ∈ Finset.range (m + 1), (-1 : Real) ^ r *
          ∑ T ∈ (Finset.univ : Finset A).powersetCard r,
            setCaptureProbability q f T) =
          ∑ r ∈ Finset.range (m + 1), (-1 : Real) ^ r *
            ∑ j ∈ Finset.range (Fintype.card A + 1),
              (Nat.choose j r : Real) *
                eventProbability q (fun s =>
                  ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j) := by
        apply Finset.sum_congr (by simp)
        intro r hr
        rw [exact_capture_count_binomial_moment q f r]
      _ = ∑ r ∈ Finset.range (m + 1),
          ∑ j ∈ Finset.range (Fintype.card A + 1),
            (-1 : Real) ^ r *
              ((Nat.choose j r : Real) *
                eventProbability q (fun s =>
                  ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j)) := by
        simp_rw [Finset.mul_sum]
      _ = ∑ j ∈ Finset.range (Fintype.card A + 1),
          ∑ r ∈ Finset.range (m + 1),
            (-1 : Real) ^ r *
              ((Nat.choose j r : Real) *
                eventProbability q (fun s =>
                  ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j)) := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr (by simp)
        intro j hj
        rw [Finset.sum_mul]
        apply Finset.sum_congr (by simp)
        intro r hr
        ring
  have hescape :
      escapeProbability q f =
        eventProbability q (fun s =>
          ((Finset.univ : Finset A).filter fun a => Captured f s a).card = 0) := by
    simp only [escapeProbability, eventProbability]
    apply Finset.sum_congr (by simp)
    intro s hs
    congr 1
    simp [Finset.card_eq_zero]
  have hescape_sum :
      escapeProbability q f =
        ∑ j ∈ Finset.range (Fintype.card A + 1),
          if j = 0 then
            eventProbability q (fun s =>
              ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j)
          else 0 := by
    rw [hescape]
    symm
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j hjrange hj
      simp [hj]
    · simp
  constructor
  · intro hm
    rw [hescape_sum, htruncation]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hjzero : j = 0
    · subst j
      rw [hpartial_zero]
      simp
    · rw [hpartial j hjzero, hm.neg_one_pow]
      simp only [if_neg hjzero, one_mul]
      exact mul_nonneg (Nat.cast_nonneg (Nat.choose (j - 1) m)) (hmass_nonneg j)
  · intro hm
    rw [htruncation, hescape_sum]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hjzero : j = 0
    · subst j
      rw [hpartial_zero]
      simp
    · rw [hpartial j hjzero, hm.neg_one_pow]
      simp only [if_neg hjzero, neg_one_mul]
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (Nat.cast_nonneg (Nat.choose (j - 1) m)))
        (hmass_nonneg j)

#print axioms escape_bonferroni_truncation

end

end D5.S0.Asymptotics.Bonferroni.TruncationBounds
