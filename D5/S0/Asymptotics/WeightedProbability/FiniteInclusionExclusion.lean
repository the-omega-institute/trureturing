/- GID: D5/S0/Asymptotics/WeightedProbability/FiniteInclusionExclusion
   generality: G
   mirror-B: D5/B/S0/Asymptotics/WeightedProbability/FiniteInclusionExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite weighted capture is the exact alternating sum of its intersection events. -/

/- Library-search audit trail (2026-08-15):
   * Pinned Mathlib provides `Finset.indicator_biUnion_eq_sum_powerset` in
     `Mathlib.Combinatorics.Enumerative.InclusionExclusion`; the exact identity
     below applies that theorem pointwise and sums with the frozen sample weight.
   * Repository searches found the first two Bonferroni bounds in
     `FiniteBonferroni`, but no exact weighted capture inclusion-exclusion identity.
   * Berman and Fryer's classical inclusion-exclusion chapter is recorded at
     `D5/L/Diagonal/berman1972inclusion` and cited by the Blueprint mirror.
-/

import D5.S0.Asymptotics.WeightedProbability.FiniteBonferroni
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

open scoped BigOperators

namespace D5.S0.Asymptotics.WeightedProbability.FiniteInclusionExclusion

open FiniteProductCapture
open FiniteBonferroni

noncomputable section

variable {A Y : Type*}

local instance (priority := low) (p : Prop) : Decidable p := Classical.propDecidable p

/-- The weighted capture event is the alternating sum of its nonempty intersection events. -/
theorem capture_event_inclusion_exclusion
    [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (f : Y -> Y) :
    eventProbability q (fun s => Exists fun a => Captured f s a) =
      ∑ T ∈ Finset.univ.powerset with T.Nonempty,
        (-1 : Real) ^ (T.card + 1) *
          eventProbability q (fun s => forall a, a ∈ T -> Captured f s a) := by
  classical
  rw [eventProbability]
  calc
    (∑ s : Sample A Y,
        if Exists fun a => Captured f s a then sampleWeight q s else 0) =
        ∑ s : Sample A Y, ∑ T ∈ Finset.univ.powerset with T.Nonempty,
          (-1 : Real) ^ (T.card + 1) *
            if (forall a, a ∈ T -> Captured f s a) then sampleWeight q s else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      simpa [Set.indicator, Set.mem_iUnion, Set.mem_iInter] using
        (Finset.indicator_biUnion_eq_sum_powerset
          (G := Real) (α := Sample A Y) Finset.univ
          (fun a => {s : Sample A Y | Captured f s a}) (sampleWeight q) s)
    _ = ∑ T ∈ Finset.univ.powerset with T.Nonempty,
        (-1 : Real) ^ (T.card + 1) *
          ∑ s : Sample A Y,
            if (forall a, a ∈ T -> Captured f s a) then sampleWeight q s else 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by rfl

/-- Under normalized marginals, capture is the complement of frozen escape probability. -/
theorem capture_event_eq_one_sub_escapeProbability
    [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (hq_sum : forall b, ∑ y, q b y = 1)
    (f : Y -> Y) :
    eventProbability q (fun s => Exists fun a => Captured f s a) =
      1 - escapeProbability q f := by
  classical
  rw [eventProbability, escapeProbability, eventProbability]
  calc
    (∑ s : Sample A Y,
        if Exists fun a => Captured f s a then sampleWeight q s else 0) =
        ∑ s : Sample A Y, (sampleWeight q s -
          if (forall a, ¬ Captured f s a) then sampleWeight q s else 0) := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : Exists fun a => Captured f s a
      · have hnot : ¬(forall a, ¬ Captured f s a) := by simpa using h
        simp [h, hnot]
      · have hnone : forall a, ¬ Captured f s a := by simpa using h
        simp [hnone]
    _ = (∑ s : Sample A Y, sampleWeight q s) -
        ∑ s : Sample A Y,
          if (forall a, ¬ Captured f s a) then sampleWeight q s else 0 := by
      exact Finset.sum_sub_distrib
        (s := Finset.univ)
        (fun s : Sample A Y => sampleWeight q s)
        (fun s : Sample A Y =>
          if (forall a, ¬ Captured f s a) then sampleWeight q s else 0)
    _ = _ := by rw [sample_weight_sum_one q hq_sum]

/-- The frozen escape probability is one minus the exact capture inclusion-exclusion sum. -/
theorem escapeProbability_inclusion_exclusion
    [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (hq_sum : forall b, ∑ y, q b y = 1)
    (f : Y -> Y) :
    escapeProbability q f =
      1 - ∑ T ∈ Finset.univ.powerset with T.Nonempty,
        (-1 : Real) ^ (T.card + 1) *
          eventProbability q (fun s => forall a, a ∈ T -> Captured f s a) := by
  have hcomplement := capture_event_eq_one_sub_escapeProbability q hq_sum f
  rw [capture_event_inclusion_exclusion] at hcomplement
  linarith

/-- The degree-one intersection sum is the frozen sum of capture probabilities. -/
theorem inclusion_exclusion_degree_one_eq_captureProbability_sum
    [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (f : Y -> Y) :
    (∑ T ∈ (Finset.univ : Finset A).powersetCard 1,
        eventProbability q (fun s => forall a, a ∈ T -> Captured f s a)) =
      ∑ a, captureProbability q f a := by
  classical
  rw [Finset.powersetCard_one]
  simp [captureProbability]

/-- The degree-two intersection sum is the frozen unordered-pair probability sum. -/
theorem inclusion_exclusion_degree_two_eq_pairProbabilitySum
    [Fintype A] [Fintype Y] [LinearOrder A]
    (q : A -> Y -> Real) (f : Y -> Y) :
    (∑ T ∈ (Finset.univ : Finset A).powersetCard 2,
        eventProbability q (fun s => forall a, a ∈ T -> Captured f s a)) =
      pairProbabilitySum q f := by
  classical
  symm
  calc
    pairProbabilitySum q f =
        ∑ a : A, ∑ b : A,
          if a < b then
            eventProbability q (fun s => Captured f s a ∧ Captured f s b)
          else 0 := by
      simp [pairProbabilitySum, pairCaptureProbability]
    _ = ∑ p ∈ ((Finset.univ : Finset A) ×ˢ Finset.univ),
        if p.1 < p.2 then
          eventProbability q (fun s => Captured f s p.1 ∧ Captured f s p.2)
        else 0 := by
      rw [Finset.sum_product]
    _ = ∑ p ∈ (((Finset.univ : Finset A) ×ˢ Finset.univ).filter
          (fun p => p.1 < p.2)),
        eventProbability q (fun s => Captured f s p.1 ∧ Captured f s p.2) := by
      rw [Finset.sum_filter]
    _ = ∑ T ∈ (Finset.univ : Finset A).powersetCard 2,
        eventProbability q (fun s => forall a, a ∈ T -> Captured f s a) := by
      refine Finset.sum_bij
        (fun p _ => {p.1, p.2})
        ?_ ?_ ?_ ?_
      · intro p hp
        have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
        exact Finset.mem_powersetCard.mpr
          ⟨by simp, Finset.card_pair (ne_of_lt hlt)⟩
      · intro p hp r hr hsets
        have hp_lt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
        have hr_lt : r.1 < r.2 := (Finset.mem_filter.mp hr).2
        have hp_one : p.1 = r.1 ∨ p.1 = r.2 := by
          have : p.1 ∈ ({r.1, r.2} : Finset A) := by
            rw [← hsets]
            simp
          simpa using this
        rcases hp_one with hp_one | hp_one
        · have hp_two : p.2 = r.1 ∨ p.2 = r.2 := by
            have : p.2 ∈ ({r.1, r.2} : Finset A) := by
              rw [← hsets]
              simp
            simpa using this
          rcases hp_two with hp_two | hp_two
          · exact False.elim ((ne_of_lt hp_lt) (hp_one.trans hp_two.symm))
          · exact Prod.ext hp_one hp_two
        · have hr_one : r.1 = p.1 ∨ r.1 = p.2 := by
            have : r.1 ∈ ({p.1, p.2} : Finset A) := by
              rw [hsets]
              simp
            simpa using this
          rcases hr_one with hr_one | hr_one
          · exact False.elim ((ne_of_lt hr_lt) (hr_one.trans hp_one))
          · have hreverse : p.2 < p.1 := by
              calc
                p.2 = r.1 := hr_one.symm
                _ < r.2 := hr_lt
                _ = p.1 := hp_one.symm
            exact False.elim (not_lt_of_ge hp_lt.le hreverse)
      · intro T hT
        have hcard : T.card = 2 := (Finset.mem_powersetCard.mp hT).2
        have hnonempty : T.Nonempty := Finset.card_pos.mp (by omega)
        let lo := T.min' hnonempty
        let hi := T.max' hnonempty
        have hlt : lo < hi := by
          exact T.min'_lt_max'_of_card (by omega)
        refine ⟨(lo, hi), ?_, ?_⟩
        · simp [lo, hi, hlt]
        · apply Finset.eq_of_subset_of_card_le
          · intro a ha
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with rfl | rfl
            · exact T.min'_mem hnonempty
            · exact T.max'_mem hnonempty
          · rw [hcard, Finset.card_pair (ne_of_lt hlt)]
      · intro p hp
        simp [eventProbability]

/-- The first two cardinality truncations of the exact identity are the frozen sandwich. -/
theorem escape_bonferroni_truncations_of_inclusion_exclusion
    [Fintype A] [Fintype Y] [LinearOrder A]
    (q : A -> Y -> Real)
    (hq_nonneg : forall b y, 0 ≤ q b y)
    (hq_sum : forall b, ∑ y, q b y = 1)
    (f : Y -> Y) :
    1 - (∑ T ∈ (Finset.univ : Finset A).powersetCard 1,
        eventProbability q (fun s => forall a, a ∈ T -> Captured f s a)) ≤
        escapeProbability q f ∧
      escapeProbability q f ≤
        1 - (∑ T ∈ (Finset.univ : Finset A).powersetCard 1,
          eventProbability q (fun s => forall a, a ∈ T -> Captured f s a)) +
          ∑ T ∈ (Finset.univ : Finset A).powersetCard 2,
            eventProbability q (fun s => forall a, a ∈ T -> Captured f s a) := by
  rw [inclusion_exclusion_degree_one_eq_captureProbability_sum,
    inclusion_exclusion_degree_two_eq_pairProbabilitySum]
  exact escape_bonferroni_bounds q hq_nonneg hq_sum f

#print axioms capture_event_inclusion_exclusion
#print axioms capture_event_eq_one_sub_escapeProbability
#print axioms escapeProbability_inclusion_exclusion
#print axioms inclusion_exclusion_degree_one_eq_captureProbability_sum
#print axioms inclusion_exclusion_degree_two_eq_pairProbabilitySum
#print axioms escape_bonferroni_truncations_of_inclusion_exclusion

end

end D5.S0.Asymptotics.WeightedProbability.FiniteInclusionExclusion
