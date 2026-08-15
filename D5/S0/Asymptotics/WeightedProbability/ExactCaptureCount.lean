/- GID: D5/S0/Asymptotics/WeightedProbability/ExactCaptureCount
   generality: G
   mirror-B: D5/B/S0/Asymptotics/WeightedProbability/ExactCaptureCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The exact mass of each finite capture count is an alternating sum of product masses. -/

/- Library-search audit trail (2026-08-16):
   * Repository searches found exact prescribed-set intersection masses and the weighted union
     inclusion-exclusion identity, but no exact distribution for the number of captured addresses.
   * Pinned Mathlib supplies `Finset.inclusion_exclusion_sum_inf_compl`, which converts absence of
     every capture outside a prescribed set into an alternating sum of larger intersections.
   * The proof applies the frozen `set_capture_probability_exact` to every resulting intersection;
     it introduces no second capture predicate or probability model.
-/

import D5.S0.Asymptotics.WeightedProbability.FiniteInclusionExclusion
import D5.S0.Asymptotics.WeightedProbability.FiniteProductSetCapture

open scoped BigOperators

namespace D5.S0.Asymptotics.WeightedProbability.ExactCaptureCount

open FiniteProductCapture
open FiniteProductSetCapture

noncomputable section

variable {A Y : Type*}

local instance (priority := low) (p : Prop) : Decidable p := Classical.propDecidable p

/-- The weighted mass of samples capturing exactly `j` addresses is the alternating sum over
prescribed `j`-sets and additional captured addresses, with every intersection evaluated by the
exact frozen product law. -/
theorem exact_capture_count_probability
    [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (hq : forall b, ∑ y, q b y = 1)
    (f : Y -> Y) (j : Nat) :
    eventProbability q (fun s =>
      ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j) =
      ∑ S ∈ (Finset.univ : Finset A).powersetCard j,
        ∑ U ∈ ((Finset.univ : Finset A) \ S).powerset,
          (-1 : Real) ^ U.card *
            ∏ b, if b ∈ S ∪ U then
              fixedPowerMass q f b (S ∪ U).card
            else collisionPowerMass q f b (S ∪ U).card := by
  classical
  have hpartition :
      eventProbability q (fun s =>
        ((Finset.univ : Finset A).filter fun a => Captured f s a).card = j) =
        ∑ S ∈ (Finset.univ : Finset A).powersetCard j,
          eventProbability q (fun s =>
            ((Finset.univ : Finset A).filter fun a => Captured f s a) = S) := by
    simp only [eventProbability]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    let C := (Finset.univ : Finset A).filter fun a => Captured f s a
    by_cases hcard : C.card = j
    · have hCmem : C ∈ (Finset.univ : Finset A).powersetCard j :=
        Finset.mem_powersetCard.mpr ⟨by simp [C], hcard⟩
      rw [if_pos hcard, Finset.sum_eq_single C]
      · simp [C]
      · intro S hS hSC
        simp [C, hSC.symm]
      · exact fun hCnot => (hCnot hCmem).elim
    · rw [if_neg hcard]
      symm
      apply Finset.sum_eq_zero
      intro S hS
      rw [if_neg]
      intro hCS
      exact hcard ((congrArg Finset.card hCS).trans (Finset.mem_powersetCard.mp hS).2)
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro S hS
  have hexactSet :
      eventProbability q (fun s =>
        ((Finset.univ : Finset A).filter fun a => Captured f s a) = S) =
        ∑ U ∈ ((Finset.univ : Finset A) \ S).powerset,
          (-1 : Real) ^ U.card *
            eventProbability q (fun s => forall a, a ∈ S ∪ U -> Captured f s a) := by
    let captureSamples : A -> Finset (Sample A Y) := fun a =>
      Finset.univ.filter fun s => Captured f s a
    let selectedWeight : Sample A Y -> Real := fun s =>
      if forall a, a ∈ S -> Captured f s a then sampleWeight q s else 0
    have hleft :
        eventProbability q (fun s =>
          ((Finset.univ : Finset A).filter fun a => Captured f s a) = S) =
          ∑ s ∈ ((Finset.univ : Finset A) \ S).inf
            (fun a => (captureSamples a)ᶜ), selectedWeight s := by
      rw [eventProbability]
      simp only [selectedWeight]
      rw [← Finset.sum_filter, ← Finset.sum_filter]
      apply Finset.sum_congr
      · ext s
        simp [captureSamples, Finset.ext_iff, Finset.mem_inf]
        constructor
        · intro h
          exact ⟨fun i hi hcaptured => hi ((h i).mp hcaptured),
            fun a ha => (h a).mpr ha⟩
        · rintro ⟨houtside, hselected⟩ a
          constructor
          · intro hcaptured
            by_contra ha
            exact houtside a ha hcaptured
          · exact hselected a
      · intro s hs
        rfl
    have hright (U : Finset A) :
        (∑ s ∈ U.inf captureSamples, selectedWeight s) =
          eventProbability q (fun s => forall a, a ∈ S ∪ U -> Captured f s a) := by
      rw [eventProbability]
      simp only [selectedWeight]
      rw [← Finset.sum_filter, ← Finset.sum_filter]
      apply Finset.sum_congr
      · ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, captureSamples,
          Finset.mem_inf, Finset.mem_union]
        constructor
        · rintro ⟨hadditional, hselected⟩ a (ha | ha)
          · exact hselected a ha
          · exact hadditional a ha
        · intro h
          exact ⟨fun a ha => h a (Or.inr ha), fun a ha => h a (Or.inl ha)⟩
      · intro s hs
        rfl
    rw [hleft]
    rw [Finset.inclusion_exclusion_sum_inf_compl]
    apply Finset.sum_congr rfl
    intro U hU
    rw [hright U]
    rw [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [hexactSet]
  apply Finset.sum_congr rfl
  intro U hU
  congr 1
  rw [show eventProbability q (fun s => forall a, a ∈ S ∪ U -> Captured f s a) =
      setCaptureProbability q f (S ∪ U) by rfl]
  exact set_capture_probability_exact q hq f (S ∪ U)

/- The normalization hypotheses and both finite domains are simultaneously inhabited. -/
example :
    let q : Fin 1 -> Unit -> Real := fun _ _ => 1
    forall b, ∑ y, q b y = 1 := by
  simp

/- The frozen independent-listing sample domain used by the theorem is inhabited. -/
example : Sample (Fin 1) Unit := ⟨fun _ => (), fun _ _ => ()⟩

#print axioms exact_capture_count_probability

end

end D5.S0.Asymptotics.WeightedProbability.ExactCaptureCount
