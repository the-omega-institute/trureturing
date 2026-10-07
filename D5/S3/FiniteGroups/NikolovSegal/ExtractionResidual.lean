/- GID: D5/S3/FiniteGroups/NikolovSegal/ExtractionResidual
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/ExtractionResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.ExtractionFreshness

set_option autoImplicit false

namespace NikolovSegal.CrossingKernel
open Equation47WordCoupling BalancedCrossing
universe u v
variable {S : Type u} [Group S] {V : Type v} [DecidableEq V]

/-- Final actual Letter residual of an accepted Extraction certificate. -/
def finalWord {D : ℕ} {W : List (Letter V S)}
    (P : Extraction D W) : List (Letter V S) :=
  match P with
  | .zero W => W
  | .step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail => finalWord tail

theorem signed_remainder_mem (x y : V) (e f a b : MulAut S) (sx sy : Bool)
    (A B C D E : List (Letter V S)) (p : V × Bool)
    (hp : p ∈ signedVariables (remainder a b A B C D E)) :
    p ∈ signedVariables (crossing x y e f a b sx sy A B C D E) := by
  simp only [signedVariables_remainder,List.mem_append] at hp
  simp only [crossing,signedVariables_append,signedVariables_var,List.mem_append,List.mem_singleton]
  tauto

/-- Twisted extraction never introduces a new signed key. -/
theorem finalWord_signed_mem {N : ℕ} {W : List (Letter V S)} (P : Extraction N W) :
    ∀ p ∈ signedVariables (finalWord P), p ∈ signedVariables W := by
  induction P with
  | zero => exact fun _ hp => hp
  | step x y hxy e f a b sx sy A B C D E havoid tail ih =>
    intro p hp
    exact signed_remainder_mem x y e f a b sx sy A B C D E p (ih p hp)

/-- All 2N distinct chosen keys are absent from the actual final residual. -/
theorem finalWord_avoids_extracted {N : ℕ} {W : List (Letter V S)} (P : Extraction N W) :
    ∀ x ∈ extractedKeys P, avoids (finalWord P) x := by
  induction P with
  | zero => simp [extractedKeys]
  | step x y hxy e f a b sx sy A B C D E havoid tail ih =>
    intro z hz
    simp only [extractedKeys,List.mem_cons] at hz
    rcases hz with rfl | rfl | hz
    · apply avoids_of_signed
      intro p hp
      exact (remainder_fresh z y a b A B C D E havoid p (finalWord_signed_mem tail p hp)).1
    · apply avoids_of_signed
      intro p hp
      exact (remainder_fresh x z a b A B C D E havoid p (finalWord_signed_mem tail p hp)).2
    · exact ih z hz

end NikolovSegal.CrossingKernel
