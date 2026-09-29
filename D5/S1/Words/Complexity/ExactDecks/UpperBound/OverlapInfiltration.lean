/- GID: D5/S1/Words/Complexity/ExactDecks/UpperBound/OverlapInfiltration
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/ExactDecks/UpperBound/OverlapInfiltration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Overlap infiltrations encode products of actual scattered counts with multiplicity. -/

import D5.S1.Words.Complexity.VivionBinomialConverseFails

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.ExactDecks.UpperBound.OverlapInfiltration

open D5.S1.Words.Complexity.VivionBinomialConverseFails

variable {A : Type*}

def overlapInfiltrations [DecidableEq A] :
    List A → List A → List (List A)
  | [], right => [right]
  | left, [] => [left]
  | a :: left, b :: right =>
      (overlapInfiltrations left (b :: right)).map (List.cons a) ++
        (overlapInfiltrations (a :: left) right).map (List.cons b) ++
          if a = b then
            (overlapInfiltrations left right).map (List.cons a)
          else []
termination_by left right => left.length + right.length
decreasing_by
  all_goals simp_wf
  omega

/-- Ordinary shuffles, retaining one list entry per choice of left/right
positions. -/
def ordinaryShuffles : List A → List A → List (List A)
  | [], right => [right]
  | left, [] => [left]
  | a :: left, b :: right =>
      (ordinaryShuffles left (b :: right)).map (List.cons a) ++
        (ordinaryShuffles (a :: left) right).map (List.cons b)
termination_by left right => left.length + right.length
decreasing_by all_goals simp_wf

/-- The product of two actual scattered-subword counts is the sum over all
overlap infiltrations.  Repeated merged words remain repeated summands, so the
identity preserves alignment multiplicity. -/
theorem scatteredCount_mul_eq_sum_overlapInfiltrations [DecidableEq A]
    (left right source : List A) :
    scatteredCount left source * scatteredCount right source =
      ((overlapInfiltrations left right).map
        (fun merged => scatteredCount merged source)).sum := by
  have hrec :
      ∀ (a b x : A) (left right source : List A),
        ((overlapInfiltrations (a :: left) (b :: right)).map
            (fun merged => scatteredCount merged (x :: source))).sum =
          ((overlapInfiltrations (a :: left) (b :: right)).map
              (fun merged => scatteredCount merged source)).sum +
            (if a = x then
              ((overlapInfiltrations left (b :: right)).map
                (fun merged => scatteredCount merged source)).sum
            else 0) +
            (if b = x then
              ((overlapInfiltrations (a :: left) right).map
                (fun merged => scatteredCount merged source)).sum
            else 0) +
            (if a = b then
              if a = x then
                ((overlapInfiltrations left right).map
                  (fun merged => scatteredCount merged source)).sum
              else 0
            else 0) := by
    intro a b x left right source
    by_cases hab : a = b
    · subst b
      simp only [overlapInfiltrations, if_pos, List.map_append,
        List.sum_append, List.map_map, Function.comp_def]
      simp only [scatteredCount, List.sum_map_add]
      by_cases hax : a = x <;> simp [hax]
      omega
    · simp only [overlapInfiltrations, if_neg hab, List.append_nil,
        List.map_append, List.sum_append, List.map_map, Function.comp_def]
      simp only [scatteredCount, List.sum_map_add]
      by_cases hax : a = x <;> by_cases hbx : b = x <;>
        simp [hax, hbx]
      all_goals omega
  induction source generalizing left right with
  | nil =>
      cases left with
      | nil =>
          cases right <;>
            simp [scatteredCount, overlapInfiltrations]
      | cons a left =>
          cases right with
          | nil => simp [scatteredCount, overlapInfiltrations]
          | cons b right =>
              by_cases hab : a = b <;>
                simp [scatteredCount, overlapInfiltrations, hab,
                  List.map_map, Function.comp_def]
  | cons x source ih =>
      cases left with
      | nil => simp [scatteredCount, overlapInfiltrations]
      | cons a left =>
          cases right with
          | nil => simp [scatteredCount, overlapInfiltrations]
          | cons b right =>
              rw [hrec]
              rw [scatteredCount, scatteredCount]
              rw [← ih (a :: left) (b :: right),
                ← ih left (b :: right), ← ih (a :: left) right,
                ← ih left right]
              by_cases hax : a = x
              · subst a
                by_cases hbx : b = x
                · subst b
                  simp
                  ring
                · have hxb : x ≠ b := Ne.symm hbx
                  simp [hbx, hxb]
                  ring
              · by_cases hbx : b = x
                · subst b
                  simp [hax]
                  ring
                · simp [hax, hbx]

private theorem length_le_of_mem_overlapInfiltrations [DecidableEq A] :
    ∀ (left right merged : List A),
      merged ∈ overlapInfiltrations left right →
        merged.length ≤ left.length + right.length := by
  intro left
  induction left with
  | nil =>
      intro right merged hmerged
      simp only [overlapInfiltrations, List.mem_singleton] at hmerged
      subst merged
      simp
  | cons a left ihLeft =>
      intro right
      induction right with
      | nil =>
          intro merged hmerged
          simp only [overlapInfiltrations, List.mem_singleton] at hmerged
          subst merged
          simp
      | cons b right ihRight =>
          intro merged hmerged
          by_cases hab : a = b
          · rw [overlapInfiltrations, if_pos hab, List.mem_append,
              List.mem_append] at hmerged
            rcases hmerged with (hleft | hright) | hshared
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
            · rw [List.mem_map] at hshared
              obtain ⟨middle, hmiddle, rfl⟩ := hshared
              have hlength := ihLeft right middle hmiddle
              simp only [List.length_cons] at hlength ⊢
              omega
          · rw [overlapInfiltrations, if_neg hab, List.append_nil,
              List.mem_append] at hmerged
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

/-- The maximal-length overlap infiltrations are exactly the ordinary
shuffles, with list equality retaining every shuffle multiplicity. -/
theorem overlapInfiltrations_filter_top_length [DecidableEq A]
    (left right : List A) :
    (overlapInfiltrations left right).filter
        (fun merged => merged.length = left.length + right.length) =
      ordinaryShuffles left right := by
  induction left generalizing right with
  | nil => simp [overlapInfiltrations, ordinaryShuffles]
  | cons a left ihLeft =>
      induction right with
      | nil => simp [overlapInfiltrations, ordinaryShuffles]
      | cons b right ihRight =>
          have hfirst :
              ((overlapInfiltrations left (b :: right)).map (List.cons a)).filter
                  (fun merged =>
                    merged.length = (a :: left).length + (b :: right).length) =
                (ordinaryShuffles left (b :: right)).map (List.cons a) := by
            rw [show (a :: left).length + (b :: right).length =
                (left.length + (b :: right).length) + 1 by simp; omega]
            rw [List.filter_map]
            have hfilter :
                (overlapInfiltrations left (b :: right)).filter
                    (((fun merged =>
                      decide (merged.length = left.length + (b :: right).length + 1)) ∘
                      List.cons a)) =
                  (overlapInfiltrations left (b :: right)).filter
                    (fun merged =>
                      decide (merged.length = left.length + (b :: right).length)) := by
              apply List.filter_congr
              intro merged _
              simp only [Function.comp_apply, List.length_cons]
              apply decide_eq_decide.mpr
              exact Nat.add_right_cancel_iff
            rw [hfilter, ihLeft (b :: right)]
          have hsecond :
              ((overlapInfiltrations (a :: left) right).map (List.cons b)).filter
                  (fun merged =>
                    merged.length = (a :: left).length + (b :: right).length) =
                (ordinaryShuffles (a :: left) right).map (List.cons b) := by
            rw [show (a :: left).length + (b :: right).length =
                ((a :: left).length + right.length) + 1 by simp; omega]
            rw [List.filter_map]
            have hfilter :
                (overlapInfiltrations (a :: left) right).filter
                    (((fun merged =>
                      decide (merged.length = (a :: left).length + right.length + 1)) ∘
                      List.cons b)) =
                  (overlapInfiltrations (a :: left) right).filter
                    (fun merged =>
                      decide (merged.length = (a :: left).length + right.length)) := by
              apply List.filter_congr
              intro merged _
              simp only [Function.comp_apply, List.length_cons]
              apply decide_eq_decide.mpr
              exact Nat.add_right_cancel_iff
            rw [hfilter, ihRight]
          have hshared :
              ((overlapInfiltrations left right).map (List.cons a)).filter
                  (fun merged =>
                    merged.length = (a :: left).length + (b :: right).length) =
                [] := by
            apply List.filter_eq_nil_iff.mpr
            intro merged hmerged
            rw [List.mem_map] at hmerged
            obtain ⟨middle, hmiddle, rfl⟩ := hmerged
            have hlength :=
              length_le_of_mem_overlapInfiltrations left right middle hmiddle
            intro htop
            have heq := of_decide_eq_true htop
            simp only [List.length_cons] at heq
            omega
          rw [overlapInfiltrations, ordinaryShuffles,
            List.filter_append, List.filter_append, hfirst, hsecond]
          by_cases hab : a = b
          · rw [if_pos hab, hshared]
            simp
          · rw [if_neg hab]
            simp

/-! ## Finite Lyndon factorization and iterated overlap -/


end D5.S1.Words.Complexity.ExactDecks.UpperBound.OverlapInfiltration
