/- GID: D5/S1/Words/Complexity/ExactDecks/UpperBound/LyndonFactorization
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/ExactDecks/UpperBound/LyndonFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every finite word factors into nonincreasing Lyndon words. -/

import D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder
import D5.S1.Words.Complexity.VivionBinomialConverseFails

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.ExactDecks.UpperBound.LyndonFactorization

open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder

variable {A : Type*}

private def insertLyndon [LinearOrder A] (u : List A) :
    List (List A) → List (List A)
  | [] => [u]
  | v :: factors =>
      if u < v then insertLyndon (u ++ v) factors
      else u :: v :: factors

private def lyndonFactors [LinearOrder A] : List A → List (List A)
  | [] => []
  | a :: word => insertLyndon [a] (lyndonFactors word)

private theorem join_insertLyndon [LinearOrder A] (u : List A) :
    ∀ factors, (insertLyndon u factors).flatten = u ++ factors.flatten := by
  intro factors
  induction factors generalizing u with
  | nil => simp [insertLyndon]
  | cons v factors ih =>
      by_cases huv : u < v
      · rw [insertLyndon, if_pos huv, ih]
        simp [List.append_assoc]
      · simp [insertLyndon, huv]

private theorem insertLyndon_isLyndon [LinearOrder A]
    (u : List A) (hu : IsLyndon u) :
    ∀ factors,
      (∀ v ∈ factors, IsLyndon v) →
      factors.Pairwise (· ≥ ·) →
      (∀ v ∈ insertLyndon u factors, IsLyndon v) ∧
        (insertLyndon u factors).Pairwise (· ≥ ·) := by
  intro factors
  induction factors generalizing u with
  | nil =>
      intro _ _
      simp [insertLyndon, hu]
  | cons v factors ih =>
      intro hlyndon hordered
      have hv : IsLyndon v := hlyndon v (by simp)
      have htailL : ∀ z ∈ factors, IsLyndon z := by
        intro z hz
        exact hlyndon z (by simp [hz])
      have htailO : factors.Pairwise (· ≥ ·) :=
        (List.pairwise_cons.mp hordered).2
      by_cases huv : u < v
      · rw [insertLyndon, if_pos huv]
        exact ih (u ++ v) (isLyndon_append hu hv huv) htailL htailO
      · rw [insertLyndon, if_neg huv]
        refine ⟨?_, ?_⟩
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hu
          · exact hlyndon z (by simp [hz])
        · rw [List.pairwise_cons]
          refine ⟨?_, hordered⟩
          intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact le_of_not_gt huv
          · exact ((List.pairwise_cons.mp hordered).1 z hz).trans
              (le_of_not_gt huv)

private theorem lyndonFactors_spec [LinearOrder A] (word : List A) :
    (lyndonFactors word).flatten = word ∧
      (∀ u ∈ lyndonFactors word, IsLyndon u) ∧
      (lyndonFactors word).Pairwise (· ≥ ·) := by
  induction word with
  | nil => simp [lyndonFactors]
  | cons a word ih =>
      have hins := insertLyndon_isLyndon [a] (by
        refine ⟨by simp, ?_⟩
        intro u v hu hv huv
        have hlen := congrArg List.length huv
        simp only [List.length_singleton, List.length_append] at hlen
        have huPos : 0 < u.length := List.length_pos_of_ne_nil hu
        have hvPos : 0 < v.length := List.length_pos_of_ne_nil hv
        omega)
        (lyndonFactors word) ih.2.1 ih.2.2
      refine ⟨?_, hins⟩
      rw [lyndonFactors, join_insertLyndon, ih.1]
      simp

end D5.S1.Words.Complexity.ExactDecks.UpperBound.LyndonFactorization
