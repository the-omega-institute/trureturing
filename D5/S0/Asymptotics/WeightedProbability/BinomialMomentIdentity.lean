/- GID: D5/S0/Asymptotics/WeightedProbability/BinomialMomentIdentity
   generality: G
   mirror-B: D5/B/S0/Asymptotics/WeightedProbability/BinomialMomentIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Capture-count binomial moments equal prescribed-set capture masses. -/

/- Library-search audit trail (2026-08-16):
   * Repository and pinned-Mathlib searches for `binomial moment`, `factorial moment`,
     `sum_choose`, and powerset/choose combinations found no theorem giving this identity.
   * Loogle returned `Finset.card_powersetCard`; `Finset.sum_powersetCard` only handles
     summands depending on subset cardinality. LeanSearch returned no usable response, and
     the Reservoir keyword search exposed no matching theorem.
   * The proof applies `Finset.card_powersetCard`, `Finset.sum_comm`, and
     `Finset.sum_eq_single` after exchanging the finite sample and subset sums.
-/

import D5.S0.Asymptotics.WeightedProbability.ExactCaptureCount

open scoped BigOperators

namespace D5.S0.Asymptotics.WeightedProbability.BinomialMomentIdentity

open FiniteProductCapture
open FiniteProductSetCapture

noncomputable section

variable {A Y : Type*}

local instance (priority := low) (p : Prop) : Decidable p := Classical.propDecidable p

/-- The `r`-th binomial moment of the capture count equals the total mass of all prescribed
`r`-address capture events. -/
theorem exact_capture_count_binomial_moment
    [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real)
    (f : Y -> Y) (r : Nat) :
    (∑ j ∈ Finset.range (Fintype.card A + 1),
        (Nat.choose j r : Real) *
          eventProbability q (fun s =>
            ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j)) =
      ∑ T ∈ (Finset.univ : Finset A).powersetCard r,
        setCaptureProbability q f T := by
  classical
  simp only [eventProbability, setCaptureProbability]
  simp_rw [Finset.mul_sum]
  calc
    (∑ j ∈ Finset.range (Fintype.card A + 1),
        ∑ s : Sample A Y,
          (Nat.choose j r : Real) *
            if ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j then
              sampleWeight q s
            else 0) =
        ∑ s : Sample A Y,
          ∑ j ∈ Finset.range (Fintype.card A + 1),
            (Nat.choose j r : Real) *
              if ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j then
                sampleWeight q s
              else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ s : Sample A Y,
          ∑ T ∈ (Finset.univ : Finset A).powersetCard r,
            if forall a, a ∈ T -> Captured f s a then sampleWeight q s else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      let C := (Finset.univ : Finset A).filter fun a => Captured f s a
      have hcard_le : C.card ≤ (Finset.univ : Finset A).card :=
        Finset.card_le_card (by simp [C])
      have hcard_mem : C.card ∈ Finset.range (Fintype.card A + 1) := by
        rw [Finset.mem_range]
        simpa using Nat.lt_succ_of_le hcard_le
      rw [Finset.sum_eq_single C.card]
      · rw [if_pos (by rfl)]
        have hcaptured (T : Finset A) :
            (forall a, a ∈ T -> Captured f s a) ↔ T ⊆ C := by
          simp only [Finset.subset_iff, C, Finset.mem_filter, Finset.mem_univ, true_and]
        simp_rw [hcaptured]
        rw [← Finset.sum_filter]
        have hfilter :
            ((Finset.univ : Finset A).powersetCard r).filter (fun T => T ⊆ C) =
              C.powersetCard r := by
          ext T
          simp [C, and_comm]
        rw [hfilter, Finset.sum_const, Finset.card_powersetCard]
        simp [nsmul_eq_mul]
      · intro j hj hjC
        simp [C, Ne.symm hjC]
      · exact fun hCnot => (hCnot hcard_mem).elim
    _ = ∑ T ∈ (Finset.univ : Finset A).powersetCard r,
          ∑ s : Sample A Y,
            if forall a, a ∈ T -> Captured f s a then sampleWeight q s else 0 := by
      rw [Finset.sum_comm]

#print axioms exact_capture_count_binomial_moment

end

end D5.S0.Asymptotics.WeightedProbability.BinomialMomentIdentity
