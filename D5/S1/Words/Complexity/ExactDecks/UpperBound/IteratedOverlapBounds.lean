/- GID: D5/S1/Words/Complexity/ExactDecks/UpperBound/IteratedOverlapBounds
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/ExactDecks/UpperBound/IteratedOverlapBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Iterated infiltrations isolate their maximal-length ordinary shuffles. -/

import D5.S1.Words.Complexity.ExactDecks.UpperBound.ShuffleScheduleComposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.ExactDecks.UpperBound.IteratedOverlapBounds

open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.ExactDecks.UpperBound.OverlapInfiltration
open private length_le_of_mem_overlapInfiltrations from
  D5.S1.Words.Complexity.ExactDecks.UpperBound.OverlapInfiltration
open private iteratedOrdinaryShuffles iteratedOverlapInfiltrations from
  D5.S1.Words.Complexity.ExactDecks.UpperBound.ShuffleScheduleComposition

variable {A : Type*}

private theorem scatteredCount_prod_eq_sum_iteratedOverlap
    [DecidableEq A] (factors : List (List A)) (source : List A) :
    (factors.map (fun word => scatteredCount word source)).prod =
      ((iteratedOverlapInfiltrations factors).map
        (fun merged => scatteredCount merged source)).sum := by
  induction factors with
  | nil => simp [iteratedOverlapInfiltrations, scatteredCount]
  | cons word factors ih =>
      rw [List.map_cons, List.prod_cons, ih]
      rw [Nat.mul_comm]
      simp only [iteratedOverlapInfiltrations]
      rw [show (((iteratedOverlapInfiltrations factors).flatMap
          (overlapInfiltrations word)).map
          (fun merged => scatteredCount merged source)).sum =
          ((iteratedOverlapInfiltrations factors).map (fun middle =>
            ((overlapInfiltrations word middle).map
              (fun merged => scatteredCount merged source)).sum)).sum by
        induction iteratedOverlapInfiltrations factors with
        | nil => simp
        | cons middle rest ihRest => simp [ihRest]]
      rw [← List.sum_map_mul_right]
      apply congrArg List.sum
      apply List.map_congr_left
      intro merged hmerged
      rw [Nat.mul_comm, scatteredCount_mul_eq_sum_overlapInfiltrations]

private theorem length_le_of_mem_iteratedOverlap [DecidableEq A] :
    ∀ (factors : List (List A)) (merged : List A),
      merged ∈ iteratedOverlapInfiltrations factors →
        merged.length ≤ (factors.map List.length).sum := by
  intro factors
  induction factors with
  | nil =>
      intro merged hmerged
      simp only [iteratedOverlapInfiltrations, List.mem_singleton] at hmerged
      subst merged
      simp
  | cons word factors ih =>
      intro merged hmerged
      simp only [iteratedOverlapInfiltrations, List.mem_flatMap] at hmerged
      obtain ⟨middle, hmiddle, hmerged⟩ := hmerged
      have h₁ := length_le_of_mem_overlapInfiltrations word middle merged hmerged
      have h₂ := ih middle hmiddle
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem iteratedOverlap_filter_top_length [DecidableEq A]
    (factors : List (List A)) :
    (iteratedOverlapInfiltrations factors).filter
        (fun merged => merged.length = (factors.map List.length).sum) =
      iteratedOrdinaryShuffles factors := by
  induction factors with
  | nil => simp [iteratedOverlapInfiltrations, iteratedOrdinaryShuffles]
  | cons word factors ih =>
      simp only [iteratedOverlapInfiltrations, iteratedOrdinaryShuffles,
        List.filter_flatMap]
      rw [← ih]
      simp only [List.map_cons, List.sum_cons]
      have aux : ∀ middles : List (List A),
          (∀ middle ∈ middles,
            middle.length ≤ (factors.map List.length).sum) →
          middles.flatMap (fun middle =>
              (overlapInfiltrations word middle).filter (fun merged =>
                merged.length = word.length + (factors.map List.length).sum)) =
            (middles.filter (fun middle =>
              middle.length = (factors.map List.length).sum)).flatMap
                (ordinaryShuffles word) := by
        intro middles hlengths
        induction middles with
        | nil => simp
        | cons middle middles ihMiddles =>
            have hmiddleLength := hlengths middle (by simp)
            have htail : ∀ z ∈ middles,
                z.length ≤ (factors.map List.length).sum := by
              intro z hz
              exact hlengths z (by simp [hz])
            simp only [List.flatMap_cons, List.filter_cons, decide_eq_true_eq]
            by_cases htop : middle.length = (factors.map List.length).sum
            · simp only [if_pos htop]
              rw [show (overlapInfiltrations word middle).filter
                  (fun merged => merged.length =
                    word.length + (factors.map List.length).sum) =
                  ordinaryShuffles word middle by
                simpa [htop] using
                  overlapInfiltrations_filter_top_length word middle]
              rw [ihMiddles htail]
              simp only [List.flatMap_cons]
            · simp only [if_neg htop]
              rw [show (overlapInfiltrations word middle).filter
                  (fun merged => merged.length =
                    word.length + (factors.map List.length).sum) = [] by
                apply List.filter_eq_nil_iff.mpr
                intro merged hmerged
                have hlength :=
                  length_le_of_mem_overlapInfiltrations word middle merged hmerged
                intro heq
                have heq' := of_decide_eq_true heq
                omega]
              rw [ihMiddles htail]
              simp only [List.nil_append]
      apply aux
      intro middle hmiddle
      exact length_le_of_mem_iteratedOverlap factors middle hmiddle

private theorem length_eq_of_mem_ordinaryShuffles :
    ∀ (left right merged : List A),
      merged ∈ ordinaryShuffles left right →
        merged.length = left.length + right.length := by
  intro left
  induction left with
  | nil =>
      intro right merged hmerged
      have hmerged' : merged = right := by
        simpa [ordinaryShuffles] using hmerged
      subst merged
      simp
  | cons a left ihLeft =>
      intro right
      induction right with
      | nil =>
          intro merged hmerged
          have hmerged' : merged = a :: left := by
            simpa [ordinaryShuffles] using hmerged
          subst merged
          simp
      | cons b right ihRight =>
          intro merged hmerged
          rw [ordinaryShuffles, List.mem_append] at hmerged
          rcases hmerged with hleft | hright
          · rw [List.mem_map] at hleft
            obtain ⟨middle, hmiddle, rfl⟩ := hleft
            have hlength := ihLeft (b :: right) middle hmiddle
            simp only [List.length_cons] at hlength ⊢
            omega
          · rw [List.mem_map] at hright
            obtain ⟨middle, hmiddle, rfl⟩ := hright
            have hlength := ihRight middle hmiddle
            simp only [List.length_cons] at hlength ⊢
            omega

private theorem length_eq_of_mem_iteratedOrdinaryShuffles :
    ∀ (factors : List (List A)) (merged : List A),
      merged ∈ iteratedOrdinaryShuffles factors →
        merged.length = (factors.map List.length).sum := by
  intro factors
  induction factors with
  | nil =>
      intro merged hmerged
      simpa [iteratedOrdinaryShuffles] using congrArg List.length
        (List.mem_singleton.mp hmerged)
  | cons word factors ih =>
      intro merged hmerged
      simp only [iteratedOrdinaryShuffles, List.mem_flatMap] at hmerged
      obtain ⟨middle, hmiddle, hmerged⟩ := hmerged
      rw [length_eq_of_mem_ordinaryShuffles word middle merged hmerged,
        ih middle hmiddle]
      simp

end D5.S1.Words.Complexity.ExactDecks.UpperBound.IteratedOverlapBounds
