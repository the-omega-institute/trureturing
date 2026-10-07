/- GID: D5/S3/FiniteGroups/NikolovSegal/ExtractionFreshness
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/ExtractionFreshness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.LetterCrossing

set_option autoImplicit false

namespace NikolovSegal.CrossingKernel
open Equation47WordCoupling BalancedCrossing
universe u v
variable {S : Type u} [Group S] {V : Type v} [DecidableEq V]

/-- Every chosen key in the actual Extraction inductive certificate. -/
def extractedKeys {D : ℕ} {W : List (Letter V S)} (P : Extraction D W) : List V :=
  match P with
  | .zero _ => []
  | .step x y _ _ _ _ _ _ _ _ _ _ _ _ _ tail => x::y::extractedKeys tail

theorem extractedKeys_length {D : ℕ} {W : List (Letter V S)} (P : Extraction D W) :
    (extractedKeys P).length = 2*D := by
  induction P with
  | zero => rfl
  | step x y hxy e f a b sx sy A B C D E havoid tail ih =>
    simp only [extractedKeys,List.length_cons]; omega

theorem signed_of_avoids {W : List (Letter V S)} {x : V} (h : avoids W x) :
    ∀ p ∈ signedVariables W, p.1 ≠ x := by
  rintro ⟨y,s⟩ hp he
  change y = x at he; subst y
  obtain ⟨l,hl,hv⟩ := List.mem_filterMap.mp hp
  cases l with
  | constant c => simp [signedVariable] at hv
  | var y g t =>
    have he : (y,t) = (x,s) := Option.some.inj hv
    cases he
    exact h g s hl

theorem remainder_fresh (x y : V) (a b : MulAut S)
    (A B C D E : List (Letter V S))
    (havoid : ∀ T ∈ [A,B,C,D,E], avoids T x ∧ avoids T y) :
    ∀ p ∈ signedVariables (remainder a b A B C D E), p.1 ≠ x ∧ p.1 ≠ y := by
  intro p hp
  have hpiece : ∀ T ∈ [A,B,C,D,E], p ∈ signedVariables T → p.1 ≠ x ∧ p.1 ≠ y := by
    intro T hT hp
    exact ⟨signed_of_avoids (havoid T hT).1 p hp,signed_of_avoids (havoid T hT).2 p hp⟩
  simp only [signedVariables_remainder,List.mem_append] at hp
  rcases hp with (((hA | hD) | hC) | hB) | hE
  · exact hpiece A (by simp) hA
  · exact hpiece D (by simp) hD
  · exact hpiece C (by simp) hC
  · exact hpiece B (by simp) hB
  · exact hpiece E (by simp) hE

theorem extractedKeys_mem {N : ℕ} {W : List (Letter V S)} (P : Extraction N W) :
    ∀ x ∈ extractedKeys P, ∃ s, (x,s) ∈ signedVariables W := by
  induction P with
  | zero => simp [extractedKeys]
  | step x y hxy e f a b sx sy A B C D E havoid tail ih =>
    intro z hz
    simp only [extractedKeys,List.mem_cons] at hz
    rcases hz with rfl | rfl | ht
    · exact ⟨sx,by simp only [crossing,signedVariables_append,signedVariables_var,List.mem_append,List.mem_singleton]; tauto⟩
    · exact ⟨sy,by simp only [crossing,signedVariables_append,signedVariables_var,List.mem_append,List.mem_singleton]; tauto⟩
    · obtain ⟨s,hs⟩ := ih z ht
      refine ⟨s,?_⟩
      simp only [signedVariables_remainder,List.mem_append] at hs
      simp only [crossing,signedVariables_append,signedVariables_var,List.mem_append,List.mem_singleton]
      tauto

/-- Global freshness is proved from the literal constructor, not supplied
as a coverage hypothesis. Every extraction selects exactly 2N distinct keys. -/
theorem extractedKeys_nodup {N : ℕ} {W : List (Letter V S)} (P : Extraction N W) :
    (extractedKeys P).Nodup := by
  induction P with
  | zero => simp [extractedKeys]
  | step x y hxy e f a b sx sy A B C D E havoid tail ih =>
    have hx : x ∉ extractedKeys tail := by
      intro hm
      obtain ⟨s,hs⟩ := extractedKeys_mem tail x hm
      exact (remainder_fresh x y a b A B C D E havoid (x,s) hs).1 rfl
    have hy : y ∉ extractedKeys tail := by
      intro hm
      obtain ⟨s,hs⟩ := extractedKeys_mem tail y hm
      exact (remainder_fresh x y a b A B C D E havoid (y,s) hs).2 rfl
    simp [extractedKeys,List.nodup_cons,hxy,hx,hy,ih]

end NikolovSegal.CrossingKernel
